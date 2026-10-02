import Mathlib
import Submission.Work.LerayHirsch.Splitting
import Submission.Work.LerayHirsch.LH
import Submission.Work.Thom.chernClass
import Submission.Work.Whitney.Cup
import Submission.Work.Thom.Gysin
import Submission.Work.Whitney.chernClass_whitneySum_pullback_eq
import Submission.Work.Thom.BundleIso_comap_exists
import Submission.Work.Cohomology.gradedComm
import Submission.Work.Gen.gysinPi_chernSplit_vanishes

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace Work.Gen

open Work.TangentClasses Work.Thom

/-! ## Two generic helpers -/

/-- `Work.Thom.cohTransport` is the degree cast `▸`. -/
theorem cohTransport_eq_cast {B : Type} [TopologicalSpace B] {p q : ℕ} (h : p = q)
    (x : Work.Thom.Coh ℤ p B) :
    Work.Thom.cohTransport h x = h ▸ x := by
  subst h
  rw [Work.Thom.cohTransport_rfl]

/-- **Even-degree commutativity of the cup product**, in `cohTransport` form: for `a` arbitrary,
`y ∈ H^{2a}` and `z ∈ H²`, `y ⌣ z = z ⌣ y` (the sign `(-1)^{2a·2} = +1`). -/
theorem cupH'_comm_even {P : Type} [TopologicalSpace P] (a : ℕ)
    (y : Work.Thom.Coh ℤ (2 * a) P) (z : Work.Thom.Coh ℤ (2 * 1) P) :
    Work.Cohomology.cupH' ℤ (Work.Whitney.ssB P) (2 * a) (2 * 1) y z
      = Work.Thom.cohTransport (Nat.add_comm (2 * a) (2 * 1)).symm
          (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB P) (2 * 1) (2 * a) z y) := by
  have hg := Work.Cohomology.gradedComm ℤ (Work.Whitney.ssB P) (2 * a) (2 * 1) y z
  have hsign : ((-1 : ℤ) ^ ((2 * a) * (2 * 1))) = 1 := by
    rw [show (2 * a) * (2 * 1) = 4 * a from by ring, pow_mul]
    simp
  rw [hsign, one_smul] at hg
  rw [← hg, cohTransport_eq_cast]
  exact (Work.Cohomology.eqRec_symm_eqRec_self3 (M := fun k => Work.Thom.Coh ℤ k P)
    (Nat.add_comm (2 * a) (2 * 1)) _).symm

/-! ## The main reduction -/

/-- The statement of `Work.Gen.exists_zeta_mul_chern_split` with the degree proof `2*(1+(n-1)) = 2*n`
as an explicit parameter (the statement's inline proof term is proof-irrelevant, so this form is
what the proof works with). -/
theorem exists_zeta_mul_chern_split_aux {B : Type} [TopologicalSpace B] [ParacompactSpace B]
    [T2Space B]
    {ι : Type} [Fintype ι] {n : ℕ} (hn : 1 ≤ n)
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (n + 1))) ι)
    (Q : VectorBundleCore ℂ (Work.LerayHirsch.ProjSpace Z) (EuclideanSpace ℂ (Fin n))
          (ι × Fin (n + 1)))
    (h : Nonempty (Work.Thom.BundleIso (Work.Thom.bundleComap Z (Work.LerayHirsch.projMap Z))
          (Work.Whitney.whitneySum (Work.LerayHirsch.tautLine Z) Q)))
    (hc : 2 * (1 + (n - 1)) = 2 * n) :
    ∃ ψ : Work.Thom.Coh ℤ (2 * (n - 1)) (Work.LerayHirsch.ProjSpace Z),
      Work.Thom.chernClass n n Q
        = ((Work.Thom.CohMap (Work.LerayHirsch.projMap Z) ℤ (2 * n)).hom
              (Work.Thom.chernClass (n + 1) n Z))
          + Work.Thom.cohTransport hc
              (Work.Whitney.cupChern 1 (n - 1) (Work.LerayHirsch.zeta Z) ψ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  -- The class `x = c_{m+1}(Q) - π^*(c_{m+1}(Z))` dies under the projection of the punctured total
  -- space of the tautological line bundle (`Work.Gen.gysinPi_chernSplit_vanishes`).
  have hvan : Work.Thom.gysinπ (Work.Thom.realification (Work.LerayHirsch.tautLine Z)) (2 * m.succ)
      (Work.Thom.chernClass m.succ m.succ Q
        - (Work.Thom.CohMap (Work.LerayHirsch.projMap Z) ℤ (2 * m.succ)).hom
            (Work.Thom.chernClass (m.succ + 1) m.succ Z)) = 0 :=
    gysinPi_chernSplit_vanishes (n := m.succ) Z Q h
  -- The Gysin sequence of that bundle: `x` lies in the range of `∪ e`.
  let T := Work.Thom.thomClassRank 1 (Nat.succ_le_succ (Nat.zero_le 0))
      (Work.LerayHirsch.tautLine Z)
  have he : T.eulerClass = Work.LerayHirsch.zeta Z := by
    rw [Work.LerayHirsch.zeta_def, Work.Thom.cohTransport_rfl]
    exact (Work.Thom.chernClass_one_top (Work.LerayHirsch.tautLine Z)).symm
  have hmem : (Work.Thom.chernClass m.succ m.succ Q
        - (Work.Thom.CohMap (Work.LerayHirsch.projMap Z) ℤ (2 * m.succ)).hom
            (Work.Thom.chernClass (m.succ + 1) m.succ Z))
      ∈ Set.range (Work.Thom.gysinEuler T (2 * (m.succ - 1))) := by
    rw [Work.Thom.gysin_exact_at_base T (2 * (m.succ - 1))]
    exact hvan
  obtain ⟨y, hy⟩ := Set.mem_range.mp hmem
  -- `∪ e` is multiplication by the Euler class `e = ζ`.
  have hchain : Work.Thom.chernClass m.succ m.succ Q
        - (Work.Thom.CohMap (Work.LerayHirsch.projMap Z) ℤ (2 * m.succ)).hom
            (Work.Thom.chernClass (m.succ + 1) m.succ Z)
      = Work.Thom.cohTransport
          (Nat.add_comm (2 * (m.succ - 1)) (2 * 1)).symm
          (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB (Work.LerayHirsch.ProjSpace Z))
            (2 * 1) (2 * (m.succ - 1)) (Work.LerayHirsch.zeta Z) y) := by
    rw [← hy, Work.Thom.gysinEuler_eq_cupEuler]
    rw [cupH'_comm_even (m.succ - 1) y T.eulerClass, he]
  -- Matching the target's degree bookkeeping: the two transports have the same (defeq) type.
  refine ⟨y, ?_⟩
  rw [Work.Whitney.cupChern_def, Work.Whitney.cohTransport_trans]
  rw [show (((Nat.mul_add 2 1 (m.succ - 1)).symm).trans hc)
      = ((Nat.add_comm (2 * (m.succ - 1)) (2 * 1)).symm) from
    Subsingleton.elim (((Nat.mul_add 2 1 (m.succ - 1)).symm).trans hc)
      ((Nat.add_comm (2 * (m.succ - 1)) (2 * 1)).symm)]
  rw [← hchain]
  abel


/-- **The `ψ`-existence (the Gysin-kernel form of the descent), key input of the crux reduction.**
Let `Z` be a complex bundle of rank `n+1 ≥ 2` over a paracompact Hausdorff base, `π : P(Z) → B` its
projectivisation, `ζ = c₁(ℓ)` and `Q` the tautological quotient in a splitting
`π^*Z ≅ ℓ ⊕ Q` (`Work.LerayHirsch.SplitsOverProj`, as supplied by
`Work.LerayHirsch.splitsOverProj_of_paracompact`), so `rank Q = n`.

**Claim.** `c_n(Q) - π^*(c_n(Z))` is divisible by `ζ` in `H^{2n}(P(Z))`.

Why: the projection `q : Z∖0 → P(Z)` is a `ℂ^*`-bundle with `q^*ζ = 0`; the descent *definition* of
`chernClass` gives `π_Z^*c_n(Z) = c_n(Q^Z)` where `Q^Z = q^*Q` is the tautological quotient over
`Z∖0` (`Work.Thom.tautQuotient` + `Work.Thom.chernClass_succ_of_le`), so
`q^*(c_n(Q) - π^*c_n(Z)) = 0`.  The kernel of `q^*` on `H^{2m}(P(Z))` is `ζ·H^{2m-2}(P(Z))`
(Gysin of the `S¹`-bundle `Z∖0 → P(Z)`; equivalently: any `x` with `q^*x = 0` has zero `ζ⁰`-component
in the Leray–Hirsch decomposition `H^{2m}(P(Z)) = ⊕_j π^*H^{2m-2j}(B)ζ^j`, hence is divisible by `ζ`).
This is the input that lets the "`ψ`-analysis" of `Submission/Work/Gen/NOTES_charnroot_reduction.md`
write `c_n(Q) = π^*c_n(Z) + ζψ` and compare coefficients in the Leray–Hirsch basis. -/
theorem exists_zeta_mul_chern_split {B : Type} [TopologicalSpace B] [ParacompactSpace B] [T2Space B]
    {ι : Type} [Fintype ι] {n : ℕ} (hn : 1 ≤ n)
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (n + 1))) ι)
    (Q : VectorBundleCore ℂ (Work.LerayHirsch.ProjSpace Z) (EuclideanSpace ℂ (Fin n))
          (ι × Fin (n + 1)))
    (h : Nonempty (Work.Thom.BundleIso (Work.Thom.bundleComap Z (Work.LerayHirsch.projMap Z))
          (Work.Whitney.whitneySum (Work.LerayHirsch.tautLine Z) Q))) :
    ∃ ψ : Work.Thom.Coh ℤ (2 * (n - 1)) (Work.LerayHirsch.ProjSpace Z),
      Work.Thom.chernClass n n Q
        = ((Work.Thom.CohMap (Work.LerayHirsch.projMap Z) ℤ (2 * n)).hom
              (Work.Thom.chernClass (n + 1) n Z))
          + Work.Thom.cohTransport (by have h := hn; omega : 2 * (1 + (n - 1)) = 2 * n)
              (Work.Whitney.cupChern 1 (n - 1) (Work.LerayHirsch.zeta Z) ψ) :=
  exists_zeta_mul_chern_split_aux hn Z Q h
    (by have h := hn; omega : 2 * (1 + (n - 1)) = 2 * n)

end Work.Gen
