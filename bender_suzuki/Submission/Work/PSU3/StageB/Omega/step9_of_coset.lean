/-
# `Work.PSU3.StageB.Omega.step9_of_coset` — Peterfalvi II, Ch. VII §2 (9)

Peterfalvi II, Ch. VII §2, item **(9)** (p. 270): for `ω ∈ Q ∖ Q₀`, the data of (5), (7), (8)
give `x, z ∈ Q₀` and `k ∈ K` with `f(ω x) = (ω z)^{kζ}`; then taking `a ∈ K` with `a² = k`
and putting `ω' = (ω x)^a`, `y = (x z)^a` one gets `ω' ∈ Q ∖ Q₀`, `y ∈ Q₀#` and
`f(ω') = (ω' y)^ζ`, with `ω'` in the `KW`-orbit of `ω`.

In the `CoarseFrame` language:

* `f (ω x) = (ω z)^{kζ}` with `k ∈ Ksub ∩ KW` and squaring is surjective on `Ksub ∩ KW`
  (it corresponds to squaring on the units of the fixed field `F` of `σE`, of odd order
  `2ⁿ - 1`); this gives the `a` of the source (`step9_sqrt_KW`);
* conjugating by `a` keeps the `Q₀`-coset and transports `ω` into its `KW`-orbit
  (`step9_orbit_conj`);
* the group computation `f(ω') = a · f(ω x) · a⁻¹`, `k = a²`, `x² = 1` and the commutativity of
  `KW` turn the hypothesis into `f(ω') = (ω' y)^ζ` (`step9_reorder`);
* finally §2 (5) (`fcan_eq_qconj`) yields `y ≠ 1`.
-/
import Mathlib
import Submission.Work.PSU3.StageB.Omega.API
import Submission.Work.PSU3.StageB.ThetaOmegaAux
import Submission.Work.PSU3.StageB.Omega.fcan_eq_qconj

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Work.RankOneUniqueness
open Classical

namespace Work.PSU3.StageB.Omega

open Work.ThmF
open Work.PSU3
open Work.PSU3.StageB

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

/-- Pure group-theoretic rearrangement used in (9): if `A² = kG` and `A` commutes with `Z`,
then the three `A`, `Z`, `kG`-factors of `A (kG Z)⁻¹ (w zz) (kG Z) A⁻¹` can be collapsed
into the single conjugate `Z⁻¹ A⁻¹ (w zz) A Z`. -/
private lemma step9_reorder (A Z kG w zz : G)
    (hAZ : A * Z = Z * A) (hA2 : A * A = kG) :
    A * (kG * Z)⁻¹ * (w * zz) * (kG * Z) * A⁻¹ = Z⁻¹ * A⁻¹ * (w * zz) * A * Z := by
  have hAZinv : A * Z⁻¹ = Z⁻¹ * A := by
    have h5 : Z * A * Z⁻¹ = A := by rw [← hAZ]; group
    calc A * Z⁻¹ = (Z⁻¹ * Z) * A * Z⁻¹ := by group
      _ = Z⁻¹ * (Z * A * Z⁻¹) := by group
      _ = Z⁻¹ * A := by rw [h5]
  have h1 : A * (kG * Z)⁻¹ = Z⁻¹ * A⁻¹ := by
    rw [mul_inv_rev, ← hA2, show (A * A)⁻¹ = A⁻¹ * A⁻¹ from by group]
    rw [show A * (Z⁻¹ * (A⁻¹ * A⁻¹)) = (A * Z⁻¹) * (A⁻¹ * A⁻¹) from by group, hAZinv]
    group
  have h2 : (kG * Z) * A⁻¹ = A * Z := by
    rw [← hA2]
    conv_lhs =>
      rw [show (A * A) * Z * A⁻¹ = A * (A * Z) * A⁻¹ from by group]
      rw [hAZ]
    group
  rw [show A * (kG * Z)⁻¹ * (w * zz) * (kG * Z) * A⁻¹
        = (A * (kG * Z)⁻¹) * (w * zz) * ((kG * Z) * A⁻¹) from by group]
  rw [h1, h2]
  group

/-- **(9), first step**: squaring is surjective on `Ksub ∩ KW`.  Via `κ`, this subgroup is the
group of `σE`-fixed units of `E n`, i.e. `Fˣ` for `F` the fixed field of `σE`; `|Fˣ| = 2ⁿ - 1`
is odd, so the (injective) squaring map is bijective. -/
private lemma step9_sqrt_KW (fr : CoarseFrame H Q t n) {k : fr.KW}
    (hk : ((k : G)) ∈ Ksub H t) :
    ∃ a : fr.KW, ((a : G) ∈ Ksub H t) ∧ a * a = k := by
  have hu : σE (((fr.κ k : (E n)ˣ) : E n)) = ((fr.κ k : (E n)ˣ) : E n) :=
    (fr.mem_K_iff k).mp hk
  obtain ⟨b, hb, hb2⟩ := Work.PSU3.StageC.exists_sqrt_fixed ((fr.κ k : (E n)ˣ) : E n) hu
  have hb0 : b ≠ 0 := by
    intro hc
    have h0 : ((fr.κ k : (E n)ˣ) : E n) = 0 := by rw [← hb2, hc]; simp
    exact (fr.κ k : (E n)ˣ).ne_zero h0
  have hv : σE ((Units.mk0 b hb0 : (E n)ˣ) : E n) = ((Units.mk0 b hb0 : (E n)ˣ) : E n) := by
    simpa using hb
  obtain ⟨a, ha⟩ := fr.K_surj (Units.mk0 b hb0) hv
  refine ⟨a, (fr.mem_K_iff a).mpr (by rw [ha]; exact hv), ?_⟩
  apply fr.κ_injective
  show fr.κ (a * a) = fr.κ k
  rw [map_mul, ha]
  apply Units.ext
  simp only [Units.val_mul, Units.val_mk0]
  rw [← pow_two]
  exact hb2

/-- **(9), second step**: conjugating the `Q₀`-coset `ω · Q₀` by `a ∈ KW` keeps it outside `Q₀`
and inside the `KW`-orbit of `ω`, and the conjugate `(x z)^a` of the `Q₀`-element `x z` stays
in `Q₀`. -/
private lemma step9_orbit_conj (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n)
    {ω : ↥Q} (hω : (ω : G) ∉ fr.Q0) {x z : ↥Q} (hx : (x : G) ∈ fr.Q0)
    (hz : (z : G) ∈ fr.Q0) (a : fr.KW) :
    qconj hS.split ⟨(a : G), fr.KW_le a.2⟩ (ω * x) ∈ orbKW hS fr ω ∧
      ((qconj hS.split ⟨(a : G), fr.KW_le a.2⟩ (ω * x) : ↥Q) : G) ∉ fr.Q0 ∧
      ((qconj hS.split ⟨(a : G), fr.KW_le a.2⟩ (x * z) : ↥Q) : G) ∈ fr.Q0 := by
  have hxQ0 : ((qconj hS.split ⟨(a:G), fr.KW_le a.2⟩ x : ↥Q) : G) ∈ fr.Q0 := by
    rw [qconj_coe]
    simpa using conj_mem_Q0_of_mem_D hS fr
      ((twoPoint H t).inv_mem (fr.KW_le a.2)) hx
  have hxzQ0 : ((qconj hS.split ⟨(a:G), fr.KW_le a.2⟩ (x*z) : ↥Q) : G) ∈ fr.Q0 := by
    rw [qconj_coe]
    simpa using conj_mem_Q0_of_mem_D hS fr
      ((twoPoint H t).inv_mem (fr.KW_le a.2)) (fr.Q0.mul_mem hx hz)
  refine ⟨?_, ?_, hxzQ0⟩
  · refine ⟨a, qconj hS.split ⟨(a:G), fr.KW_le a.2⟩ x, hxQ0, ?_⟩
    apply Subtype.ext
    simp only [kact_coe, qconj_coe, Subgroup.coe_mul]
    group
  · intro hc
    have hQ0 : ((qconj hS.split ⟨(a:G), fr.KW_le a.2⟩ (ω*x) : ↥Q) : G) *
        ((qconj hS.split ⟨(a:G), fr.KW_le a.2⟩ x : ↥Q) : G)⁻¹ ∈ fr.Q0 :=
      fr.Q0.mul_mem hc (fr.Q0.inv_mem hxQ0)
    have heq : ((qconj hS.split ⟨(a:G), fr.KW_le a.2⟩ (ω*x) : ↥Q) : G) *
        ((qconj hS.split ⟨(a:G), fr.KW_le a.2⟩ x : ↥Q) : G)⁻¹ =
        (a:G)⁻¹ * (ω:G) * (a:G) := by
      simp only [qconj_coe, Subgroup.coe_mul]
      group
    have hmem : (a:G)⁻¹ * (ω:G) * (a:G) ∈ fr.Q0 := by rw [← heq]; exact hQ0
    have hb := conj_mem_Q0_of_mem_D hS fr (fr.KW_le a.2) hmem
    have hωQ0 : (ω:G) ∈ fr.Q0 := by
      have h2 : (a:G) * ((a:G)⁻¹ * (ω:G) * (a:G)) * (a:G)⁻¹ = (ω:G) := by group
      rw [h2] at hb
      exact hb
    exact hω hωQ0

theorem step9_of_coset {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}
    (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    {ω : ↥Q} (hω : (ω : G) ∉ fr.Q0)
    (hreal : ∃ x z : ↥Q, (x : G) ∈ fr.Q0 ∧ (z : G) ∈ fr.Q0 ∧
      ∃ k : fr.KW, ((k : G) ∈ Work.ThmF.Ksub H t) ∧
        Work.PSU3.StageB.fcan hS.split (ω * x) =
          Work.PSU3.StageB.qconj hS.split
            (⟨((k * fr.ζ : fr.KW) : G), fr.KW_le (k * fr.ζ).2⟩ :
              ↥(Submission.Blueprint.twoPoint H t)) (ω * z)) :
    ∃ ω' : ↥Q, ω' ∈ Work.PSU3.StageB.orbKW hS fr ω ∧ (ω' : G) ∉ fr.Q0 ∧
      ∃ y : ↥Q, (y : G) ∈ fr.Q0 ∧ y ≠ 1 ∧
        Work.PSU3.StageB.fcan hS.split ω' =
          Work.PSU3.StageB.qconj hS.split (Work.PSU3.StageB.zetaD fr) (ω' * y) := by
  rcases hreal with ⟨x, z, hx, hz, k, hkK, heq⟩
  obtain ⟨a, haK, ha2⟩ := step9_sqrt_KW fr hkK
  obtain ⟨horb, hω'Q0, hyQ0⟩ := step9_orbit_conj hS fr hω hx hz a
  have hx1 : ((ω * x : ↥Q) : G) ≠ 1 := by
    intro hc
    refine hω ?_
    have h2 : (ω : G) = ((ω * x : ↥Q) : G) * (x : G)⁻¹ := by
      rw [Subgroup.coe_mul]; group
    rw [h2, hc, one_mul]
    exact fr.Q0.inv_mem hx
  have hfq : (fcan hS.split (qconj hS.split ⟨(a:G), fr.KW_le a.2⟩ (ω*x)) : G)
      = (a:G) * (fcan hS.split (ω*x) : G) * (a:G)⁻¹ := by
    rw [fcan_qconj hS.split hx1 ⟨(a:G), fr.KW_le a.2⟩,
        tconj_eq_inv hS.split fr haK, inv_inv]
  have hfq2 : (fcan hS.split (ω*x) : G)
      = ((k:G) * (fr.ζ:G))⁻¹ * ((ω:G)*(z:G)) * ((k:G) * (fr.ζ:G)) := by
    have h := congrArg (fun u : ↥Q => (u : G)) heq
    simp only [qconj_coe, Subgroup.coe_mul] at h
    exact h
  have hmain : fcan hS.split (qconj hS.split ⟨(a:G), fr.KW_le a.2⟩ (ω * x)) =
      qconj hS.split (zetaD fr) (qconj hS.split ⟨(a:G), fr.KW_le a.2⟩ (ω * x) *
        qconj hS.split ⟨(a:G), fr.KW_le a.2⟩ (x * z)) := by
    apply Subtype.ext
    simp only [qconj_coe, Subgroup.coe_mul, zetaD]
    rw [hfq, hfq2]
    have hx2 : (x:G) * (x:G) = 1 := Q0_mul_self fr hx
    have hAZ : (a:G) * (fr.ζ:G) = (fr.ζ:G) * (a:G) := KW_comm fr a fr.ζ
    have hA2 : (a:G) * (a:G) = (k:G) := by
      have h := congrArg (fun u : fr.KW => (u:G)) ha2
      rwa [Subgroup.coe_mul] at h
    rw [show (a:G) * (((k:G) * (fr.ζ:G))⁻¹ * ((ω:G)*(z:G)) * ((k:G) * (fr.ζ:G))) * (a:G)⁻¹
          = (a:G) * ((k:G) * (fr.ζ:G))⁻¹ * ((ω:G)*(z:G)) * ((k:G) * (fr.ζ:G)) * (a:G)⁻¹
          from by group]
    rw [step9_reorder (a:G) (fr.ζ:G) (k:G) (ω:G) (z:G) hAZ hA2]
    rw [show (fr.ζ:G)⁻¹ * (((a:G)⁻¹ * ((ω:G)*(x:G)) * (a:G)) *
            ((a:G)⁻¹ * ((x:G)*(z:G)) * (a:G))) * (fr.ζ:G)
          = (fr.ζ:G)⁻¹ * (a:G)⁻¹ * ((ω:G)*(z:G)) * (a:G) * (fr.ζ:G) from by
            rw [show (a:G)⁻¹ * ((ω:G)*(x:G)) * (a:G) *
                    ((a:G)⁻¹ * ((x:G)*(z:G)) * (a:G))
                  = (a:G)⁻¹ * (ω:G) * ((x:G)*(x:G)) * (z:G) * (a:G) from by group]
            rw [hx2]
            group]
  have hneG : ((qconj hS.split ⟨(a:G), fr.KW_le a.2⟩ (x * z) : ↥Q) : G) ≠ 1 :=
    (fcan_eq_qconj hS fr hω'Q0 hyQ0 (a := zetaD fr) hmain).1
  refine ⟨qconj hS.split ⟨(a:G), fr.KW_le a.2⟩ (ω * x), horb, hω'Q0,
    qconj hS.split ⟨(a:G), fr.KW_le a.2⟩ (x * z), hyQ0, ?_, hmain⟩
  intro h1
  exact hneG (by rw [h1, Subgroup.coe_one])

end Work.PSU3.StageB.Omega
