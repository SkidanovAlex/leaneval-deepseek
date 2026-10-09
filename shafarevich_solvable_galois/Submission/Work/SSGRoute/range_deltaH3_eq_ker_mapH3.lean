import Mathlib
import Submission.Work.SSGRoute.kummerBase_euler_connectingH3_descent
import Submission.Work.SSGRoute.H3Map.mapC3c_mem_Z3_mem_B3
import Submission.Work.SSGRoute.H3Map.range_deltaH3_le_ker_mapH3
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Exactness at `H³(G,M)`: `range δ³ = ker H³(ι)`

For a short exact sequence `0 → M →^{ι} N →^{π} P → 0` of discrete `G`-modules, the long exact
sequence in continuous cohomology continues one step beyond
`Work.SSGRoute.range_mapH2_eq_ker_deltaH3` (exactness at `H²(G,P)`):

  `H¹(G,P) → H²(G,M) → H²(G,N) → H²(G,P) →^{δ³} H³(G,M) →^{ι_*} H³(G,N)`.

Here `δ³ = ShortExactSeq.deltaH3` is the second connecting map
(`SSGRoute/kummerBase_euler_connectingH3_descent.lean`) and `ι_* = H3Map.mapH3 S.iota` is the
coefficient functoriality of `H³` (`SSGRoute/H3Map/mapC3c_mem_Z3_mem_B3.lean`).  This file proves the
exactness at `H³(G,M)`:

  `range δ³ = ker (H³(ι))`.

* **`range δ³ ≤ ker H³(ι)`** (the easy inclusion, proved in
  `SSGRoute/H3Map/range_deltaH3_le_ker_mapH3.lean`): `deltaZ3 c` is `ι⁻¹ ∘ d²` of a lift `ñ` of `c`;
  applying `ι` to it returns `d²ñ`, and `ñ` is locally constant, so `ι ∘ deltaZ3 c` is a
  `3`-coboundary of `N`.  Here it is imported as `Work.SSGRoute.H3Map.range_deltaH3_le_ker_mapH3`.
* **`ker H³(ι) ≤ range δ³`** (the substantive inclusion, proved below): if `ι ∘ c` is a
  `3`-coboundary of `N`, say `ι ∘ c = d² b` with `b` locally constant, then `a := π ∘ b` is a
  continuous `2`-cocycle of `P` (because `π ∘ ι = 0`), and comparing the canonical lift of `a` with
  `b` — two lifts of the same cochain — shows that `δ³ [a] = [c]` modulo `3`-coboundaries.

The file also records the cochain-level identity `mapZ3_iota_deltaZ3` underlying the easy inclusion
(`ι ∘ deltaZ3 c = d² (liftCochain2 c)`) and the two elementary `H³` facts `H3_induction_on` and
`H3π_eq_iff` used by the hard inclusion.
-/

open scoped Classical

namespace Work.SSGRoute

open Work.AbsoluteKummer

variable {G : Type*} [TopologicalSpace G] [Group G]

/-! ## The induction principle for `H³` and the computation rule of `H³π` -/

/-- Induction principle for `H³`: it suffices to check a predicate on the classes of continuous
`3`-cocycles.  (The analogue of `Work.AbsoluteKummer.SES.H2_induction_on` one degree up.) -/
theorem H3_induction_on {M : Type*} [AddCommGroup M] [DistribMulAction G M]
    {C : H3 (M := M) G → Prop} (x : H3 (M := M) G)
    (h : ∀ c : Z3 (M := M) G, C (H3π G c)) : C x := by
  obtain ⟨c, rfl⟩ := QuotientAddGroup.mk'_surjective
    ((B3 (M := M) G).comap (Z3 (M := M) G).subtype) x
  exact h c

/-- Two classes in `H³(G,M)` agree iff their `3`-cocycles differ by a `3`-coboundary. -/
theorem H3π_eq_iff {M : Type*} [AddCommGroup M] [DistribMulAction G M]
    (c c' : Z3 (M := M) G) :
    H3π G c = H3π G c' ↔
      ((c - c' : Z3 (M := M) G) : G × G × G → M) ∈ B3 (M := M) G := by
  rw [H3π, QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply,
    QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_comap]
  rfl

/-- A locally constant `2`-cochain killed by `d²` is a continuous `2`-cocycle. -/
theorem mem_Z2_of_isLocallyConstant_d2_eq_zero {A : Type*} [AddCommGroup A]
    [DistribMulAction G A] {c : G × G → A} (hc : Work.GroupCohomology.d2 G A c = 0)
    (hlc : Work.AbsoluteKummer.IsLocallyConstant c) : c ∈ Z2 G A := by
  rw [Z2, AddSubgroup.mem_inf, Work.GroupCohomology.Z2_eq_ker_d2, AddMonoidHom.mem_ker,
    mem_C2c_iff]
  exact ⟨hc, hlc⟩

/-! ## The cochain identity `ι ∘ deltaZ3 c = d² (lift of c)` -/

/-- **The connecting cocycle is a lift of `d²`**: applying `ι` to `deltaZ3 c` returns `d²` of the
canonical lift of `c`.  In other words `H³(ι) ∘ δ³` is the class of `d² (liftCochain2 c)`, a
`3`-coboundary. -/
theorem mapZ3_iota_deltaZ3 {M N P : Type _} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [DistribMulAction G M] [DistribMulAction G N] [DistribMulAction G P]
    [IsTopologicalGroup G] (S : ShortExactSeq G M N P) (c : Z2 G P) :
    ((H3Map.mapZ3 S.iota S.iota_equivariant (S.deltaZ3 c)) : G × G × G → N)
      = Work.GroupCohomology.d2 G N (S.liftCochain2 (c : G × G → P)) := by
  have hpi : Work.GroupCohomology.d2 G P
      (fun p => S.pi (S.liftCochain2 (c : G × G → P) p)) = 0 := by
    rw [show (fun p : G × G => S.pi (S.liftCochain2 (c : G × G → P) p)) = (c : G × G → P)
      from funext fun p => S.pi_liftCochain2 _ p]
    exact d2_eq_zero_of_mem_Z2 c.2.1
  funext p
  rw [H3Map.mapZ3_apply, S.deltaZ3_eq_deltaCochain3 c]
  exact S.iota_iotaInv (S.pi_d2_of_d2_pi_eq_zero hpi p)

/-! ## The hard inclusion: `ker H³(ι) ≤ range δ³` -/

/-- **Exactness at `H³(G,M)` (the substantive inclusion)**: every `3`-cohomology class of `M` whose
image under `ι_*` dies comes from the connecting map `δ³ : H²(G,P) → H³(G,M)`.

If `ι ∘ c = d² b` for a locally constant `2`-cochain `b` of `N`, then `a := π ∘ b` is a continuous
`2`-cocycle of `P`: its `d²` is `π (d² b) = π (ι ∘ c) = 0`.  The canonical lift of `a` and `b` have
the same image under `π`, so their connecting cochains differ by a `3`-coboundary, and the
connecting cochain of `b` is `ι⁻¹ (d² b) = ι⁻¹ (ι ∘ c) = c`.  Hence `δ³ [a] = [c]`. -/
theorem ker_mapH3_le_range_deltaH3 {M N P : Type _} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] [DistribMulAction G M] [DistribMulAction G N] [DistribMulAction G P]
    [IsTopologicalGroup G] (S : ShortExactSeq G M N P) :
    (H3Map.mapH3 S.iota S.iota_equivariant).ker ≤ S.deltaH3.range := by
  intro y hy
  rw [AddMonoidHom.mem_ker] at hy
  revert hy
  refine H3_induction_on y
    (C := fun z => H3Map.mapH3 S.iota S.iota_equivariant z = 0 → z ∈ S.deltaH3.range) ?_
  intro c hc
  -- `ι ∘ c` is a `3`-coboundary of `N`
  rw [H3Map.mapH3_H3π, H3π_eq_zero_iff, mem_B3_iff] at hc
  obtain ⟨b, hblc, hb⟩ := hc
  have hbpt : ∀ p : G × G × G,
      Work.GroupCohomology.d2 G N b p = S.iota ((c : G × G × G → M) p) := by
    intro p
    have h := congrFun hb p
    rw [H3Map.mapZ3_apply] at h
    exact h
  -- `a := π ∘ b` is a continuous `2`-cocycle of `P`
  have hloc_a : Work.AbsoluteKummer.IsLocallyConstant (fun p : G × G => S.pi (b p)) :=
    Work.AbsoluteKummer.IsLocallyConstant.map S.pi hblc
  have hd2a : Work.GroupCohomology.d2 G P (fun p : G × G => S.pi (b p)) = 0 := by
    rw [d2_comp S.pi S.pi_equivariant b]
    funext p
    rw [hbpt p, S.pi_iota]
    rfl
  have ha : (fun p : G × G => S.pi (b p)) ∈ Z2 G P :=
    mem_Z2_of_isLocallyConstant_d2_eq_zero hd2a hloc_a
  let aZ : Z2 G P := ⟨fun p : G × G => S.pi (b p), ha⟩
  -- the canonical lift of `a` and `b` are two lifts of the same cochain
  have hpi : ∀ p : G × G, S.pi (S.liftCochain2 (aZ : G × G → P) p) = S.pi (b p) := by
    intro p
    rw [S.pi_liftCochain2]
  have hcoc : Work.GroupCohomology.d2 G P
      (fun p => S.pi (S.liftCochain2 (aZ : G × G → P) p)) = 0 := by
    rw [show (fun p : G × G => S.pi (S.liftCochain2 (aZ : G × G → P) p))
        = ((aZ : Z2 G P) : G × G → P) from funext fun p => S.pi_liftCochain2 _ p]
    exact d2_eq_zero_of_mem_Z2 aZ.2.1
  have hB := S.deltaCochain3_sub_mem_B3
    (S.isLocallyConstant_liftCochain2 (c := (aZ : G × G → P)) hloc_a) hblc hpi hcoc
  -- the connecting cochain of `b` is `c` itself
  have hcb : S.deltaCochain3 b = (c : G × G × G → M) := by
    funext p
    show S.iotaInv (Work.GroupCohomology.d2 G N b p) = (c : G × G × G → M) p
    rw [hbpt p, S.iotaInv_iota]
  rw [hcb] at hB
  -- hence `δ³ [a] = [c]`
  refine ⟨H2π G P aZ, ?_⟩
  rw [S.deltaH3_H2π, H3π_eq_iff]
  have hcoe : ((S.deltaZ3 aZ - c : Z3 (M := M) G) : G × G × G → M)
      = S.deltaCochain3 (S.liftCochain2 (aZ : G × G → P)) - (c : G × G × G → M) := by
    funext p
    rw [AddSubgroup.coe_sub, Pi.sub_apply, S.deltaZ3_eq_deltaCochain3 aZ]
    rfl
  rw [hcoe]
  exact hB

/-! ## Exactness at `H³(G,M)` -/

theorem range_deltaH3_eq_ker_mapH3 {G : Type*} [TopologicalSpace G] [Group G]
    [IsTopologicalGroup G] {M N P : Type _} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [DistribMulAction G M] [DistribMulAction G N] [DistribMulAction G P]
    (S : Work.AbsoluteKummer.ShortExactSeq G M N P) :
    S.deltaH3.range = (Work.SSGRoute.H3Map.mapH3 S.iota S.iota_equivariant).ker :=
  le_antisymm (H3Map.range_deltaH3_le_ker_mapH3 S) (ker_mapH3_le_range_deltaH3 S)

end Work.SSGRoute
