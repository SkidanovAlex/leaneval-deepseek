import Mathlib
import Submission.Work.ThmF.ChV3.Ctx
import Submission.Work.ThmF.ChV3.step1
import Submission.Work.ThmF.Tools.External
import Submission.Work.ThmF.ChV12.prop3
import Submission.Work.ThmF.ChV12.prop3_quot_cyclic
import Submission.Work.ThmF.ChV12.prop3_card_fixed_pow
import Submission.Work.ThmF.ChV12.lemma2b
import Submission.Work.ThmF.ChV3.A_aux.W_sup_P_eq_centD_of_FT

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.A_reduction`

Peterfalvi II Ch. V §3, step (1), last clause.  In the standing context `CtxF H Q t s r P`
(`G` simple in situation (B0)–(B2), split rank-one data `H = Q ⋊ D`, structure identity
`t s t = r⁻¹ t r`, and `(F1)`: `P ≤ V = centD H t` of prime order with `C_G(P)` of 2-rank 1),

  `C_D(P) = Σ · P`,  with `D = twoPoint H t`, `V = centD H t`, `K = Kset H t = J(D,t)`,
  `W = C_V(K)`, and `Σ = Sig H t P = C_W(P)`.

## What is proved here (sorry-free)

* `twoPoint_inf_centralizer_le_centD` — **the `(F1)`-reduction**: `C_D(P) ≤ V`.
  For `x ∈ D` and `g = x⁻¹ (t x t⁻¹)`: `g ∈ K` (`t` normalises `D`, and `t g t⁻¹ = g⁻¹`), and
  `g ∈ C_G(P)` (`x ∈ C_G(P)` and `P ≤ V = C_D(t)`).  Hence `g = 1` by `(F1)`, i.e. `x ∈ C_D(t) = V`.
  (This is the step `C_D(P) = C_K(P)·C_V(P) = C_V(P)` of the source.)

* `le_normalizer_W` — `P` (indeed `V`) normalises `W = C_V(K)`, so `W ⊔ P = W · P` as sets.

* `eq_of_W_sup_P_eq_centD` — **the assembly**: if `V = W · P` (i.e. `W H t ⊔ P = centD H t`), then
  `C_D(P) = Σ ⊔ P`.  So the requested identity is *equivalent* to `V = W ⊔ P` (given the first
  lemma and `P` commutative, which holds as `|P|` is prime).

## The missing input and the status of the requested statement

`V = W ⊔ P` is proved in the source from §1 Prop. 3 (the field/automorphism structure of
`Q₀ ⋊ (D/W)`), which needs §1 Prop. 2 (`K = J(D,t)` cyclic normal in `D`).  Every proof of Prop. 2
in this workspace (`ChV12.Ksub_cyclic_normal`, `ChV12.L5prop2`, `PSU3.StageA.*`) needs
`FeitThompsonProp` (Appendix X: `D` has odd order, so `D` is solvable by the odd order theorem) —
except in the branches `V = ⊥` and `W ≠ ⊥`; the branch `V ≠ ⊥`, `W = ⊥` is precisely the project's
open input `ChV12.L5prop2_caseWbot` (`ThmF/Pending/L5prop2_caseWbot.lean.txt`,
`PSU3/StageA/Ksub_eq_Kset_of_W_bot.lean`).  In that branch the identity proved here becomes
`C_D(P) = P`, i.e. `C_V(P) = P`, whose only known route is that same field structure.

Consequently `CtxF H Q t s r P` + `ChIIFourProp` alone do **not** determine the requested identity;
`CtxF` is the source's context with `FeitThompsonProp` (and hence §1 Prop. 2/3) dropped.  This is
the defect the project has already recorded for the sibling steps `ChV3/step1`, `step3`, `step4`,
`step6`, `step8`, `step9`, `step10`, `step12`, `step13` (`outcome: wrong` in the host state: "it
silently drops `FeitThompsonProp`"), and it is what `ChV3/Chain.lean` (`ChV3Prop`, which threads
`FeitThompsonProp` and the other literature inputs) repairs.  With `FeitThompsonProp` added, the
clause `V = W ⊔ P` is a theorem of this library (delegated as
`ThmF/ChV3/A_aux/W_sup_P_eq_centD_of_FT`), and the requested identity follows by the assembly
below.

No counterexample exists: Théorème F (`ThmFProp`) makes `CtxF` contradictory together with
`IsSimpleGroup G`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

open scoped Pointwise

namespace Work.ThmF.ChV3

open Classical Submission.Blueprint

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}

/-! ## The `(F1)`-reduction `C_D(P) ≤ V` -/

/-- **`C_D(P) ≤ V`.**  If `x ∈ D = twoPoint H t` centralises `P`, then `x ∈ V = centD H t`.

Put `g = x⁻¹ (t x t⁻¹)`.  Since `t` normalises `D` and inverts `K = J(D,t)`, `g ∈ K`; since
`x ∈ C_G(P)` and `P ≤ V = C_D(t)`, `g ∈ C_G(P)`.  Hypothesis `(F1)`, through
`Kset_inf_centralizer_eq_bot`, gives `K ∩ C_G(P) = {1}`, so `g = 1`, i.e. `x ∈ C_D(t) = V`. -/
theorem twoPoint_inf_centralizer_le_centD (hC4 : ChIIFourProp) (c : CtxF H Q t s r P) :
    twoPoint H t ⊓ Subgroup.centralizer (P : Set G) ≤ centD H t := by
  intro x hx
  obtain ⟨hxD, hxC⟩ := Subgroup.mem_inf.mp hx
  -- `t` is an involution
  have ht2 : t * t = 1 := by
    have h1 := pow_orderOf_eq_one t
    rw [c.split.invol, pow_two] at h1
    exact h1
  have hφφ : MulAut.conj t * MulAut.conj t = 1 := by
    rw [← map_mul, ht2, map_one]
  have hφφ' : ∀ y : G, MulAut.conj t (MulAut.conj t y) = y := fun y => by
    rw [← MulAut.mul_apply, hφφ, MulAut.one_apply]
  -- `t` normalises `D`
  have htN : t ∈ Subgroup.normalizer ((twoPoint H t : Subgroup G) : Set G) :=
    Work.ThmF.normalizes_twoPoint_of_data (Work.ThmF.IsSplitRankOne.toData c.split)
  have htD : t * x * t⁻¹ ∈ twoPoint H t :=
    (Subgroup.mem_normalizer_iff.mp htN x).mp hxD
  -- the key element
  set g : G := x⁻¹ * (t * x * t⁻¹) with hgdef
  have hgD : g ∈ twoPoint H t :=
    (twoPoint H t).mul_mem ((twoPoint H t).inv_mem hxD) htD
  have hginv : t * g * t⁻¹ = g⁻¹ := by
    have hg' : g = x⁻¹ * (MulAut.conj t) x := by rw [hgdef, MulAut.conj_apply]
    calc t * g * t⁻¹ = (MulAut.conj t) g := by rw [MulAut.conj_apply]
      _ = (MulAut.conj t) (x⁻¹ * (MulAut.conj t) x) := by rw [hg']
      _ = ((MulAut.conj t) x)⁻¹ * x := by rw [map_mul, map_inv, hφφ']
      _ = (x⁻¹ * (MulAut.conj t) x)⁻¹ := by group
      _ = g⁻¹ := by rw [hg']
  -- `g` centralises `P`
  have hgC : g ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have hpV : p ∈ centD H t := c.P_le hp
    have hpt : t * p = p * t :=
      (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hpV).2).symm
    have hpt' : p * t⁻¹ = t⁻¹ * p := by
      calc p * t⁻¹ = t⁻¹ * (t * (p * t⁻¹)) := by group
        _ = t⁻¹ * ((t * p) * t⁻¹) := by group
        _ = t⁻¹ * ((p * t) * t⁻¹) := by rw [← hpt]
        _ = t⁻¹ * p := by group
    have hpx : p * x = x * p := Subgroup.mem_centralizer_iff.mp hxC p hp
    have hpxi : p * x⁻¹ = x⁻¹ * p := by
      have h3 : p * x * p⁻¹ = x := by rw [hpx]; group
      calc p * x⁻¹ = p * x⁻¹ * p⁻¹ * p := by group
        _ = (p * x * p⁻¹)⁻¹ * p := by
          rw [show p * x⁻¹ * p⁻¹ = (p * x * p⁻¹)⁻¹ by group]
        _ = x⁻¹ * p := by rw [h3]
    calc p * g = p * x⁻¹ * (t * x * t⁻¹) := by rw [hgdef]; group
      _ = x⁻¹ * p * (t * x * t⁻¹) := by rw [hpxi]
      _ = x⁻¹ * (p * t) * x * t⁻¹ := by group
      _ = x⁻¹ * (t * p) * x * t⁻¹ := by rw [← hpt]
      _ = x⁻¹ * t * (p * x) * t⁻¹ := by group
      _ = x⁻¹ * t * (x * p) * t⁻¹ := by rw [hpx]
      _ = x⁻¹ * t * x * (p * t⁻¹) := by group
      _ = x⁻¹ * t * x * (t⁻¹ * p) := by rw [hpt']
      _ = x⁻¹ * (t * x * t⁻¹) * p := by group
      _ = g * p := by rw [hgdef]
  have hgK : g ∈ Work.ThmF.Kset H t := Work.ThmF.mem_Kset_iff.mpr ⟨hgD, hginv⟩
  have hbot := Work.ThmF.ChV3.Kset_inf_centralizer_eq_bot c.sit hC4 c.split c.P_le c.F1
  have hg1 : g = 1 := by
    have hmem : g ∈ ({1} : Set G) := by
      rw [← hbot]
      exact ⟨hgK, hgC⟩
    exact Set.mem_singleton_iff.mp hmem
  -- hence `x` centralises `t`
  have h2 : x⁻¹ * (t * x * t⁻¹) = 1 := by rw [← hgdef]; exact hg1
  have h3 : t * x * t⁻¹ = x := by
    have h4 : x * (x⁻¹ * (t * x * t⁻¹)) = x * 1 := by rw [h2]
    calc t * x * t⁻¹ = x * (x⁻¹ * (t * x * t⁻¹)) := by group
      _ = x * 1 := h4
      _ = x := by rw [mul_one]
  have htx : t * x = x * t := by
    have h5 : t * x * t⁻¹ * t = x * t := by rw [h3]
    rwa [mul_assoc, inv_mul_cancel, mul_one] at h5
  exact Subgroup.mem_inf.mpr
    ⟨hxD, Subgroup.mem_centralizer_singleton_iff.mpr htx.symm⟩

/-! ## `V` normalises `W = C_V(K)` -/

/-- `V = centD H t` normalises `W = C_V(K)`: it normalises `K = Kset H t`, hence its centraliser.
Consequently `P ≤ V` lies in the normalizer of `W`, so `W ⊔ P = W · P` as sets. -/
theorem le_normalizer_W (hC4 : ChIIFourProp) (c : CtxF H Q t s r P) :
    P ≤ Subgroup.normalizer (Work.ThmF.W H t : Set G) := by
  have hKinv : ∀ v ∈ centD H t, ∀ k ∈ Work.ThmF.Kset H t, v * k * v⁻¹ ∈ Work.ThmF.Kset H t :=
    fun v hv k hk => conj_mem_Kset_of_mem_centD hv hk
  intro p hp
  have hpV : p ∈ centD H t := c.P_le hp
  have hpV' : p⁻¹ ∈ centD H t := (centD H t).inv_mem hpV
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨hxV, hxC⟩ := Subgroup.mem_inf.mp hx
    have hxC' : ∀ h ∈ Work.ThmF.Kset H t, h * x = x * h :=
      Subgroup.mem_centralizer_iff.mp hxC
    refine Subgroup.mem_inf.mpr ⟨(centD H t).mul_mem ((centD H t).mul_mem hpV hxV) hpV', ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hk' : p⁻¹ * k * p ∈ Work.ThmF.Kset H t := by
      simpa using hKinv p⁻¹ hpV' k hk
    have hkx : (p⁻¹ * k * p) * x = x * (p⁻¹ * k * p) := hxC' (p⁻¹ * k * p) hk'
    calc k * (p * x * p⁻¹) = p * ((p⁻¹ * k * p) * x) * p⁻¹ := by group
      _ = p * (x * (p⁻¹ * k * p)) * p⁻¹ := by rw [hkx]
      _ = (p * x * p⁻¹) * k := by group
  · obtain ⟨hxV, hxC⟩ := Subgroup.mem_inf.mp hx
    have hxC' : ∀ h ∈ Work.ThmF.Kset H t, h * (p * x * p⁻¹) = (p * x * p⁻¹) * h :=
      Subgroup.mem_centralizer_iff.mp hxC
    have h3 : x = p⁻¹ * (p * x * p⁻¹) * p := by group
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [h3]
      exact (centD H t).mul_mem ((centD H t).mul_mem hpV' hxV) hpV
    · rw [h3, Subgroup.mem_centralizer_iff]
      intro k hk
      have hk' : p * k * p⁻¹ ∈ Work.ThmF.Kset H t := hKinv p hpV k hk
      have hky : (p * k * p⁻¹) * (p * x * p⁻¹) = (p * x * p⁻¹) * (p * k * p⁻¹) :=
        hxC' (p * k * p⁻¹) hk'
      calc k * (p⁻¹ * (p * x * p⁻¹) * p) = p⁻¹ * ((p * k * p⁻¹) * (p * x * p⁻¹)) * p := by group
        _ = p⁻¹ * ((p * x * p⁻¹) * (p * k * p⁻¹)) * p := by rw [hky]
        _ = (p⁻¹ * (p * x * p⁻¹) * p) * k := by group

/-! ## The assembly: `V = W · P` implies the requested identity -/

/-- **The assembly.**  If `V = W · P` (`W H t ⊔ P = centD H t`), then `C_D(P) = Σ ⊔ P`.

With `C_D(P) ≤ V` (`twoPoint_inf_centralizer_le_centD`) we get `C_D(P) = C_V(P)`.  Given
`v ∈ C_V(P)`, write `v = w·p` with `w ∈ W`, `p ∈ P` (the decomposition `V = W·P` as sets, valid
because `P` normalises `W`); as `|P|` is prime, `P` is commutative, so `p ∈ C_G(P)` and
`w = v·p⁻¹ ∈ C_W(P)`.  Hence `C_V(P) ≤ C_W(P)·P`, and the reverse inclusion is immediate. -/
theorem eq_of_W_sup_P_eq_centD (hC4 : ChIIFourProp) (c : CtxF H Q t s r P)
    (hV : Work.ThmF.W H t ⊔ P = centD H t) :
    twoPoint H t ⊓ Subgroup.centralizer (P : Set G) = Sig H t P ⊔ P := by
  -- `P` has prime order, hence is commutative
  have hPle : P ≤ Subgroup.centralizer (P : Set G) := by
    haveI : Fact (Nat.card P).Prime := ⟨c.P_prime⟩
    haveI : IsCyclic ↥P := isCyclic_of_prime_card rfl
    haveI : IsMulCommutative ↥P := IsCyclic.isMulCommutative
    intro p hp
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact congrArg Subtype.val
      (isMulCommutative_iff.mp (inferInstance : IsMulCommutative ↥P) ⟨q, hq⟩ ⟨p, hp⟩)
  -- `V = W · P` as sets
  have hmul : (centD H t : Set G) = (Work.ThmF.W H t : Set G) * (P : Set G) := by
    rw [← hV]
    exact Subgroup.coe_mul_of_right_le_normalizer_left (Work.ThmF.W H t) P
      (le_normalizer_W hC4 c)
  refine le_antisymm ?_ ?_
  · -- `C_D(P) ≤ Σ ⊔ P`
    intro x hx
    obtain ⟨hxD, hxC⟩ := Subgroup.mem_inf.mp hx
    have hxV : x ∈ centD H t := twoPoint_inf_centralizer_le_centD hC4 c ⟨hxD, hxC⟩
    have hxWP : x ∈ (Work.ThmF.W H t : Set G) * (P : Set G) := by
      rw [← hmul]; exact hxV
    obtain ⟨w, hw, p, hp, hwp⟩ := hxWP
    have hwC : w ∈ Subgroup.centralizer (P : Set G) := by
      have hpC : p⁻¹ ∈ Subgroup.centralizer (P : Set G) := hPle (P.inv_mem hp)
      have hw' : w = x * p⁻¹ := by rw [← hwp]; group
      rw [hw']
      exact (Subgroup.centralizer (P : Set G)).mul_mem hxC hpC
    have hwSig : w ∈ Sig H t P := Subgroup.mem_inf.mpr ⟨hw, hwC⟩
    have hmem : w * p ∈ Sig H t P ⊔ P :=
      (Sig H t P ⊔ P).mul_mem (Subgroup.mem_sup_left hwSig) (Subgroup.mem_sup_right hp)
    simpa [← hwp] using hmem
  · -- `Σ ⊔ P ≤ C_D(P)`
    refine sup_le ?_ ?_
    · refine le_inf ?_ inf_le_right
      calc Sig H t P ≤ Work.ThmF.W H t := inf_le_left
        _ ≤ centD H t := Work.ThmF.W_le_centD H t
        _ ≤ twoPoint H t := inf_le_left
    · exact le_inf (c.P_le.trans inf_le_left) hPle

/-! ## The statement

`A_reduction` carries only `ChIIFourProp` and `CtxF`, *without* `FeitThompsonProp`; it is *not*
derivable from those hypotheses with this library: by the two lemmas above it is equivalent to
`V = W ⊔ P`, whose only route is §1 Prop. 3 (⟸ §1 Prop. 2 ⟸ Appendix X + Feit–Thompson),
unavailable in the branch `V ≠ ⊥`, `W = ⊥` (the project's open `ChV12.L5prop2_caseWbot`).

**2026-10-05.**  With `FeitThompsonProp` the missing input is supplied by
`Work.ThmF.ChV3.A_aux.W_sup_P_eq_centD_of_FT`, and the statement follows from
`eq_of_W_sup_P_eq_centD`; that form below carries `hFT`.  The `hFT`-free statement remains open. -/

theorem A_reduction_of_FT (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC4 : Submission.Blueprint.ChIIFourProp) {G : Type} [Group G] [Finite G]
    {H Q : Subgroup G} {t s r : G} {P : Subgroup G} (c : CtxF H Q t s r P) :
    twoPoint H t ⊓ Subgroup.centralizer (P : Set G) = Sig H t P ⊔ P :=
  eq_of_W_sup_P_eq_centD hC4 c
    (Work.ThmF.ChV3.A_aux.W_sup_P_eq_centD_of_FT hFT hC4 c)


end Work.ThmF.ChV3
