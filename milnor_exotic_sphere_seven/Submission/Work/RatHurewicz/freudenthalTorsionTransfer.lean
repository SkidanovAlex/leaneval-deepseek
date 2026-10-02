import Mathlib
import Submission.Work.Stems.stableStemsTorsion_of_stable3
import Submission.Work.RatHurewicz.homotopyExcision
import Submission.Work.RatHurewicz.pair_les
import Submission.Work.RatHurewicz.SphereConnectivity
import Submission.Work.RatHurewicz.SuspGeom
import Submission.Work.RatHurewicz.SuspAux
import Submission.Work.RatHurewicz.SuspRelPi
import Submission.Work.StemsB.pi_contractible
import Submission.Work.StemsB.basepoint_transport
import Submission.Work.Stems.mulEquiv_of_homotopyEquiv
import Submission.Work.RatHurewicz.subsingleton_zerothHomotopy_of_homotopyEquiv
import Submission.Work.Stems.sphereConnectivity

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

open scoped Topology unitInterval Topology.Homotopy

namespace Work.RatHurewicz

noncomputable section

/-!
# Freudenthal's suspension theorem, torsion form

The proof of `Work.RatHurewicz.freudenthalTorsionTransfer` given here is the geometric one:
`S^{n+1}` is written as the union of the open upper hemisphere `B = suspB n` and the complement
`C = suspC n` of the north pole (both contractible discs), with intersection the thickened equator
`B ∩ C = suspA n`, a deformation retract of the equator `Sⁿ` (`suspAHomotopyEquiv`).

Blakers–Massey (`Work.RatHurewicz.homotopyExcision`) applies to the open triad, with the
connectivity of the two pairs coming from the connectors `suspBConn`, `suspCConn` on the pieces
through `Work.RatHurewicz.relPiVanishingOfConnector`; together with the exact sequence of the pair
`(S^{n+1}, C)` (`pair_les`) and the two homotopy equivalences this yields a *surjective*
homomorphism
`π_{n+i+2}(S^{n+1}) →* π_{n+i+1}(Sⁿ)` (the suspension), which is all that is needed to transport
torsion. -/

/-- **A surjectivity consequence of the exact sequence of a pair.**  If `i : A → X`, `k ≥ 1` and
`π_{k+1}(A) = 0`, then the boundary map `π_{k+2}(X) → π_{k+1}(X,A)` is surjective. -/
theorem pair_d_surjective {X : Type} [TopologicalSpace X] {A : Type} [TopologicalSpace A]
    (i : C(A, X)) (a₀ : A) (k : ℕ) (hk : 1 ≤ k)
    (hA : Subsingleton (HomotopyGroup (Fin (k + 1)) A a₀)) :
    ∃ d : HomotopyGroup (Fin (k + 2)) X (i a₀) →*
        RelHomotopyGroup i a₀ (k + 1), Function.Surjective d := by
  obtain ⟨del, d, h1, h2, h3, h4⟩ := pair_les i a₀ k hk
  refine ⟨d, fun y => ?_⟩
  have hy : (Work.StemsB.πmap (homotopyFibreFst i a₀) k
      (homotopyFibreBasepoint i a₀)) y = 1 := hA.elim _ 1
  exact (h4 y).mp hy

/-- A surjective function transports `Subsingleton` from its source to its target. -/
theorem subsingleton_of_surjective {α β : Type*} {f : α → β} (hf : Function.Surjective f)
    (h : Subsingleton α) : Subsingleton β :=
  ⟨fun a b => by
    obtain ⟨a', rfl⟩ := hf a
    obtain ⟨b', rfl⟩ := hf b
    rw [@Subsingleton.elim α h a' b']⟩

/-- **A surjective homomorphism transfers torsion to its target.** -/
theorem torsion_of_surjective {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Surjective f)
    (hG : ∀ g : G, ∃ N : ℕ, 0 < N ∧ g ^ N = 1) :
    ∀ h : H, ∃ N : ℕ, 0 < N ∧ h ^ N = 1 := by
  intro h
  obtain ⟨g, rfl⟩ := hf h
  obtain ⟨N, hN, hpow⟩ := hG g
  exact ⟨N, hN, by rw [← map_pow, hpow, map_one]⟩

/-- **Points of the sphere model of the statement are joined by a path** (for `n ≥ 1`). -/
theorem joined_sphere {n : ℕ} (hn : 1 ≤ n) (x y : Sph n) : Joined x y := by
  have hπ0 : Subsingleton (HomotopyGroup (Fin 0) (Sph n) x) :=
    Work.Stems.sphereConnectivity n 0 hn x
  let e0 := HomotopyGroup.pi0EquivZerothHomotopy (X := Sph n) (x := x)
  have hZ : Subsingleton (ZerothHomotopy (Sph n)) :=
    subsingleton_of_surjective e0.surjective hπ0
  exact Quotient.exact (hZ.allEq (Quotient.mk _ x) (Quotient.mk _ y))

/-- **Freudenthal's suspension result, in the form the STEMS contract consumes** (Serre blueprint
§3, last line; `Work.Serre.SerreFreudenthal` is the same statement).

For `1 ≤ n` and `i + 3 ≤ n`: if every class of `π_{n+i+2}(S^{n+1})` is of finite order, then every
class of `π_{n+i+1}(Sⁿ)` is of finite order.  Indeed, by Freudenthal's suspension result the
suspension map `π_{n+i+1}(Sⁿ) → π_{n+i+2}(S^{n+1})` is an isomorphism in the range
`n + i + 1 ≤ 2n - 2`, which is exactly `i + 3 ≤ n`, and an isomorphism carries torsion to torsion.

Route, using the tools of this directory and of the area STEMS-B (no suspension functor is needed,
only the two hemispheres of the target sphere).  Write `S^{n+1}` as the union of two thickened
hemispheres `B`, `C` with `B ∩ C` a thickened equator (path connected, so
`Work.RatHurewicz.homotopyExcision` applies in its open-cover form, and `StemsB/SphHemi.lean`
provides the hemisphere geometry).  The pairs `(B, B∩C)` and `(C, B∩C)` are `(n+1)`-connected,
because `B ∩ C` is homotopy equivalent to `Sⁿ` and `B` to `D^{n+1}`, with
`π_j(Sⁿ) = 0` for `j < n` (`Work.Stems.sphereConnectivity`) and the connecting maps of the pair
sequences (`Work.RatHurewicz.pair_les`).  Blakers–Massey in the range `j ≤ p + q` then identifies
`π_j(S^{n+1}, C) ≅ π_j(B, B∩C)`, and combining this with the exact sequences of the pairs
`(S^{n+1}, C)` and `(B, B∩C)` — both degenerate because `C` and `B` are contractible (discs) —
gives
`π_j(S^{n+1}) ≅ π_j(S^{n+1}, C) ≅ π_j(B, B∩C) ≅ π_{j-1}(B∩C) ≅ π_{j-1}(Sⁿ)` for
`2 ≤ j ≤ 2n`, i.e. `π_j(S^{n+1}) ≅ π_{j-1}(Sⁿ)` for `2 ≤ j ≤ 2n`; with `j = n+i+2` this is the
range `i + 3 ≤ n` requested.  The composite iso is the suspension, and torsion is carried along an
isomorphism of groups. -/
theorem freudenthalTorsionTransfer : Work.Stems.FreudenthalTorsionTransfer := by
  intro n i hn hi htop x₀ α
  -- `i + 3 ≤ n` forces `n ≥ 3`
  have hn3 : 3 ≤ n := by omega
  -- the base point of the triad: a point of the thickened equator
  let xc : ↥(suspB n ∩ suspC n) := suspAIncl n (Work.StemsB.eLast n)
  -- `↥(B ∩ C)` has the connectivity of `Sⁿ`
  have hconnA : ∀ k : ℕ, k < n → Subsingleton (HomotopyGroup (Fin k) ↥(suspB n ∩ suspC n) xc) :=
    fun k hk => subsingleton_homotopyGroup_suspA n k hk xc
  -- Blakers–Massey for the open triad `(S^{n+1}; B, C)`
  have hexc : Function.Bijective (excisionMap (suspB n) (suspC n) xc (n + i)) := by
    refine homotopyExcision (Sph (n + 1)) (suspB n) (suspC n) (suspB_union_suspC n)
      (isOpen_suspB n) (isOpen_suspC n) xc (n - 1) (n - 1) ?_ ?_ (n + i) ?_
    · intro k hk
      exact relPiVanishingOfConnector (suspBConn n) (interInclLeft (suspB n) (suspC n)) xc k
        (hconnA k (by omega))
    · intro k hk
      exact relPiVanishingOfConnector (suspCConn n) (interInclRight (suspB n) (suspC n)) xc k
        (hconnA k (by omega))
    · omega
  -- the base point of `C` corresponding to `xc`
  let cC : ↥(suspC n) := ⟨xc.1, xc.2.2⟩
  -- the boundary map of the pair `(S^{n+1}, C)`, surjective because `C` is contractible
  haveI hCcontr : ContractibleSpace ↥(suspC n) := suspC_contractible n
  obtain ⟨dC, hdC⟩ := pair_d_surjective (setIncl (suspC n)) cC (n + i) (by omega)
    (Work.StemsB.pi_contractible (n + i) cC)
  -- the three isomorphisms of the chain
  let e1 : RelHomotopyGroup (setIncl (suspC n)) cC (n + i + 1) ≃*
      RelHomotopyGroup (interInclLeft (suspB n) (suspC n)) xc (n + i + 1) :=
    (MulEquiv.ofBijective (excisionMap (suspB n) (suspC n) xc (n + i)) hexc).symm
  let e2 := (Work.Stems.mulEquiv_of_homotopyEquiv (N := Fin (n + i + 1))
      (relPiHomotopyEquiv (suspBConn n) (interInclLeft (suspB n) (suspC n)) xc)
      (homotopyFibreBasepoint (interInclLeft (suspB n) (suspC n)) xc)).some
  let e3 := (Work.Stems.mulEquiv_of_homotopyEquiv (N := Fin (n + i + 1))
      (suspAHomotopyEquiv n) xc).some
  -- the composite surjection, i.e. the suspension
  let F : HomotopyGroup (Fin (n + i + 2)) (Sph (n + 1)) (setIncl (suspC n) cC) →*
      HomotopyGroup (Fin (n + i + 1)) (Sph n) ((suspAHomotopyEquiv n).toFun xc) :=
    e3.toMonoidHom.comp (e2.toMonoidHom.comp (e1.toMonoidHom.comp dC))
  have hF : Function.Surjective F :=
    e3.surjective.comp (e2.surjective.comp (e1.surjective.comp hdC))
  -- torsion of the source
  have htors : ∀ β : HomotopyGroup (Fin (n + i + 2)) (Sph (n + 1)) (setIncl (suspC n) cC),
      ∃ N : ℕ, 0 < N ∧ β ^ N = 1 := fun β => htop (setIncl (suspC n) cC) β
  -- torsion of the target
  have hq : ∀ γ : HomotopyGroup (Fin (n + i + 1)) (Sph n) ((suspAHomotopyEquiv n).toFun xc),
      ∃ N : ℕ, 0 < N ∧ γ ^ N = 1 :=
    torsion_of_surjective F hF htors
  -- change the base point to the one requested by the statement
  obtain ⟨γpath⟩ := joined_sphere hn ((suspAHomotopyEquiv n).toFun xc) x₀
  obtain ⟨eX⟩ := Work.StemsB.basepoint_transport (n + i) γpath
  obtain ⟨N, hN, hpowN⟩ := hq (eX.symm α)
  refine ⟨N, hN, ?_⟩
  have h := congrArg eX hpowN
  rw [map_pow, MulEquiv.apply_symm_apply, map_one] at h
  exact h

end

end Work.RatHurewicz
