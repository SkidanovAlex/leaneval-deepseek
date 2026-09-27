import Mathlib
import Submission.Work.Cohomology.MVApply

open CategoryTheory Simplicial Opposite

namespace Work.Cohomology

open Submission.Cohomology

/-- **The connecting map of the Mayer–Vietoris sequence is injective when the two pieces are
acyclic.**  For subcomplexes `A, B` with `A ⊔ B = ⊤` and `k ≥ 1`, if `H A ℚ k` and `H B ℚ k` are
subsingletons then the connecting map `mvConnecting S A B hAB k : H (A ∩ B) ℚ k → H S ℚ (k+1)` is
injective.

Proof plan.  Let `x` be a class with `mvConnecting x = 0`, and write `x = H.mk c hc`.  By
`mvConnecting_mk`, `H.mk (mvDeltaRep S A B hAB k c) _ = 0`, so
`mvDeltaRep S A B hAB k c ∈ boundaries S ℚ (k+1)`: there is `q` with
`coboundary S ℚ k q = mvDeltaRep S A B hAB k c`.  With `(a,b) := mvLift S A B k c`, the identity
`mvAlpha_mvDeltaRep` gives `mvD S A B k (mvLift S A B k c) = mvAlpha S A B (k+1) (mvDeltaRep … c)`
(here the exactness in degree `k+1` is used through `mvD_mvLift_mem_range`), whence
`mvD S A B k (mvLift S A B k c) = mvD S A B k (mvAlpha S A B k q)` by `mvAlpha_coboundary`; so
`p := mvLift S A B k c - mvAlpha S A B k q` is a cocycle of the product complex (`mvD p = 0`).
Its two components are `k`-cocycles of `A` and of `B`, hence coboundaries because `k ≥ 1` and
`H A ℚ k`, `H B ℚ k` are subsingletons (use `Submission.Cohomology.mem_boundaries_of_subsingleton`
and case on `k = m+1`): `p.1 = coboundary A ℚ m a'`, `p.2 = coboundary B ℚ m b'`.  Then
`c = mvBeta S A B k (mvLift S A B k c) = mvBeta S A B k (mvAlpha S A B k q + mvD S A B m (a',b'))
= 0 + coboundary (A ∩ B) ℚ m (mvBeta S A B m (a', b'))` by `mvBeta_mvLift`, `mvBeta_coboundary`
and `mvBeta_comp_mvAlpha`, so `c ∈ boundaries (A ∩ B) ℚ k` and `x = 0`. -/
theorem mvConnecting_injective (S : SSet.{0}) (A B : S.Subcomplex) (hAB : A ⊔ B = ⊤) (k : ℕ)
    (hk : 1 ≤ k) (hA : Subsingleton (Submission.Cohomology.H A ℚ k))
    (hB : Subsingleton (Submission.Cohomology.H B ℚ k)) :
    Function.Injective (Submission.Cohomology.mvConnecting S A B hAB k) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  -- write `x` as the class of a cocycle of `A ⊓ B`
  obtain ⟨c, hc, hxc⟩ : ∃ (c : Cochain (A ⊓ B : S.Subcomplex) ℚ k),
      ∃ hc : c ∈ cycles (A ⊓ B : S.Subcomplex) ℚ k, H.mk c hc = x :=
    ⟨(Quot.out x).1, (Quot.out x).2, Quot.out_eq x⟩
  have hx1 : mvConnecting S A B hAB k (H.mk c hc) = 0 := by rw [hxc]; exact hx
  -- `k = m + 1` with `m ≥ 0`
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [mvConnecting_mk S A B hAB (m+1) hc] at hx1
  -- the connecting map of `c` is a coboundary of `S`
  have hmem : mvDeltaRep S A B hAB (m+1) c ∈ boundaries S ℚ (m+1+1) := by
    have hkey : H.mk (mvDeltaRep S A B hAB (m+1) c)
        (mvDeltaRep_mem_cycles S A B hAB (m+1) (fun j => mvExact S A B hAB j) hc)
        = H.mk (0 : Cochain S ℚ (m+1+1)) (Submodule.zero_mem _) := hx1
    have := (H.mk_eq_mk_iff (mvDeltaRep S A B hAB (m+1) c)
      (0 : Cochain S ℚ (m+1+1))
      (mvDeltaRep_mem_cycles S A B hAB (m+1) (fun j => mvExact S A B hAB j) hc)
      (Submodule.zero_mem _)).mp hkey
    simpa using this
  obtain ⟨q, hq⟩ := (mem_boundaries_succ (n := m+1) (mvDeltaRep S A B hAB (m+1) c)).mp hmem
  -- the corrected lift `p = mvLift c - mvAlpha q` is a cocycle of the product complex
  set p : Cochain A ℚ (m+1) × Cochain B ℚ (m+1) :=
    mvLift S A B (m+1) c - mvAlpha S A B (m+1) q with hp
  have hpd : mvD S A B (m+1) p = 0 := by
    rw [hp, map_sub]
    have h1 : mvD S A B (m+1) (mvLift S A B (m+1) c)
        = mvAlpha S A B (m+1+1) (mvDeltaRep S A B hAB (m+1) c) :=
      (mvAlpha_mvDeltaRep S A B hAB (m+1) (fun j => mvExact S A B hAB j) hc).symm
    have h2 : mvD S A B (m+1) (mvAlpha S A B (m+1) q)
        = mvAlpha S A B (m+1+1) (mvDeltaRep S A B hAB (m+1) c) := by
      rw [← mvAlpha_coboundary S A B (m+1) q, hq]
    rw [h1, h2, sub_self]
  have hp1 : p.1 ∈ cycles A ℚ (m+1) := by
    have h := congrArg Prod.fst hpd
    simpa using h
  have hp2 : p.2 ∈ cycles B ℚ (m+1) := by
    have h := congrArg Prod.snd hpd
    simpa using h
  -- the components are coboundaries because `H A ℚ (m+1)` and `H B ℚ (m+1)` are subsingletons
  have hb1 : p.1 ∈ boundaries A ℚ (m+1) := mem_boundaries_of_subsingleton A hA hp1
  have hb2 : p.2 ∈ boundaries B ℚ (m+1) := mem_boundaries_of_subsingleton B hB hp2
  obtain ⟨a', ha'⟩ := (mem_boundaries_succ (n := m) p.1).mp hb1
  obtain ⟨b', hb'⟩ := (mem_boundaries_succ (n := m) p.2).mp hb2
  have hpd_eq : mvD S A B m (a', b') = p := by
    apply Prod.ext
    · simpa [ha'] using mvD_fst S A B m (a', b')
    · simpa [hb'] using mvD_snd S A B m (a', b')
  have hmvLift : mvLift S A B (m+1) c = p + mvAlpha S A B (m+1) q := by
    rw [hp]; abel
  have hzero : mvBeta S A B (m+1) (mvAlpha S A B (m+1) q) = 0 := by
    have h := LinearMap.congr_fun (mvBeta_comp_mvAlpha S A B (m+1)) q
    simpa [LinearMap.comp_apply] using h
  -- hence `c` itself is a coboundary of `A ⊓ B`
  have hc_bd : c ∈ boundaries (A ⊓ B : S.Subcomplex) ℚ (m+1) := by
    refine (mem_boundaries_succ (n := m) c).mpr ⟨mvBeta S A B m (a', b'), ?_⟩
    rw [← mvBeta_coboundary S A B m (a', b'), hpd_eq, ← mvBeta_mvLift S A B (m+1) c,
      hmvLift, map_add, hzero, add_zero]
  rw [← hxc]
  change Submodule.Quotient.mk (p := boundariesInCycles (A ⊓ B : S.Subcomplex) ℚ (m+1))
    ⟨c, hc⟩ = 0
  rw [Submodule.Quotient.mk_eq_zero]
  exact hc_bd

end Work.Cohomology
