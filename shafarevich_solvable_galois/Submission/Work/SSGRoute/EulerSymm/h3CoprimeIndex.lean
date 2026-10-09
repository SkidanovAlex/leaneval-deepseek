import Mathlib
import Submission.Work.SSGRoute.PT.ClassFormation
import Submission.Work.SSGRoute.H3Map.mapC3c_mem_Z3_mem_B3
import Submission.Work.SSGRoute.PTdualControl.h3Exactness
import Submission.Work.SSGRoute.EulerSymm.h3Functoriality
import Submission.Work.SSGRoute.EulerSymm.cosetReps
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `p`-Sylow step in degree `3`: `H³(G,M) ↪ H³(U,M)` for `[G:U]` prime to `p`

For a group `G`, a finite-index subgroup `U ≤ G` of index prime to `p` and a finite
`𝔽_p[G]`-module `M`, vanishing of `H³(U,M)` implies vanishing of `H³(G,M)`.

`M` is a `G`-equivariant retract of the coinduced module `Coind_U^G M`:

* the *diagonal* `diag m = (x ↦ x⁻¹ • m)` is a well defined `G`-equivariant additive map (the
  relation `f (x * u) = u⁻¹ • f x` defining `Coind` holds for *any* action of `U` on `M`);
* the *averaging* `avg f = [G:U]⁻¹ • ∑_{t ∈ T} t • f t`, where `T` is a complete set of left-coset
  representatives (`EulerSymm/cosetReps.lean`), is `G`-equivariant: the summand `t ↦ t • f t` is
  right-`U`-invariant, so the sum only depends on the *set* of cosets
  (`sum_eq_of_isCosetReps`), which is what turns the coset translation into a reindexing.  It
  retracts the diagonal by `∑_{t ∈ T} t • (t⁻¹ • m) = |T| • m = [G:U] • m` with `[G:U]` inverted
  in `𝔽_p` — the hypothesis `Nat.Coprime U.index p`.

Functoriality (`EulerSymm/h3Functoriality`) then gives `mapH3 avg ∘ mapH3 diag = mapH3 (avg ∘ diag)
= 1`, so `mapH3 diag` is injective, and Shapiro in degree `3` (taken as the explicit hypothesis
`hsh`, so that this file does not depend on the unproved node `PT.shapiro_H3_coind`) identifies
`H³(G, Coind_U^G M)` with `H³(U,M) = 0`.

Nothing here assumes that `U` is normal or that `U` acts trivially on `M`.
-/

set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

namespace Work.SSGRoute.EulerSymm

open Classical

section Summand

variable {G : Type*} [Group G] {M : Type*} [AddCommGroup M] [DistribMulAction G M]

/-- The right-`U`-invariant summand `x ↦ x • f x` of the averaging on a coinduced module. -/
def coindSummand (U : Subgroup G) (f : Work.SSGRoute.PT.Coind G U M) : G → M := fun x => x • f x

/-- **The summand of the averaging is invariant under right multiplication by `U`** — this is
exactly the relation defining the coinduced module. -/
theorem coindSummand_mul (U : Subgroup G) (f : Work.SSGRoute.PT.Coind G U M) (x : G) (u : U) :
    coindSummand U f (x * (u : G)) = coindSummand U f x := by
  rw [coindSummand, Work.SSGRoute.PT.Coind.coe_mul]
  show (x * (u : G)) • ((u⁻¹ : U) • f x) = x • f x
  rw [show (u⁻¹ : U) • f x = ((u⁻¹ : U) : G) • f x from rfl, ← mul_smul, mul_assoc,
    Subgroup.coe_inv, mul_inv_cancel, mul_one]

/-- The averaging sum over a finite set of representatives. -/
noncomputable def coindAvgSum (U : Subgroup G) (T : Finset G) :
    Work.SSGRoute.PT.Coind G U M →+ M :=
  { toFun := fun f => ∑ t ∈ T, coindSummand U f t
    map_zero' := by simp [coindSummand]
    map_add' := fun f g => by
      have h1 : (∑ t ∈ T, t • ((f : G → M) t + (g : G → M) t))
          = (∑ t ∈ T, t • (f : G → M) t) + ∑ t ∈ T, t • (g : G → M) t := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun t _ => smul_add t _ _)
      simpa [coindSummand] using h1 }

theorem coindAvgSum_apply (U : Subgroup G) (T : Finset G)
    (f : Work.SSGRoute.PT.Coind G U M) :
    coindAvgSum U T f = ∑ t ∈ T, t • f t := rfl

/-- **The averaging sum only depends on the set of cosets**, not on the chosen representatives. -/
theorem coindAvgSum_eq_of_isCosetReps (U : Subgroup G) {T T' : Finset G}
    (hT : IsCosetReps U T) (hT' : IsCosetReps U T') (f : Work.SSGRoute.PT.Coind G U M) :
    coindAvgSum U T f = coindAvgSum U T' f := by
  rw [coindAvgSum_apply, coindAvgSum_apply]
  exact sum_eq_of_isCosetReps hT hT' _ (fun x u => coindSummand_mul U f x u)

/-- **The averaging sum is `G`-equivariant.** -/
theorem coindAvgSum_smul (U : Subgroup G) {T : Finset G} (hT : IsCosetReps U T)
    (g : G) (f : Work.SSGRoute.PT.Coind G U M) :
    coindAvgSum U T (g • f) = g • coindAvgSum U T f := by
  have hterm : ∀ t : G, coindSummand U (g • f) t = g • coindSummand U f (g⁻¹ * t) := by
    intro t
    show t • (g • f) t = g • ((g⁻¹ * t) • f (g⁻¹ * t))
    rw [Work.SSGRoute.PT.Coind.smul_apply, ← mul_smul, mul_inv_cancel_left]
  -- the coset translation `t ↦ g⁻¹ * t` only permutes the *set* of cosets
  have hinner : (∑ t ∈ T, coindSummand U f (g⁻¹ * t)) = ∑ t ∈ T, coindSummand U f t := by
    rw [← Finset.sum_image (f := fun s => coindSummand U f s)
      (fun a _ b _ h => mul_left_cancel h)]
    exact coindAvgSum_eq_of_isCosetReps U (isCosetReps_image_mul hT g⁻¹) hT f
  calc coindAvgSum U T (g • f) = ∑ t ∈ T, coindSummand U (g • f) t := rfl
    _ = ∑ t ∈ T, g • coindSummand U f (g⁻¹ * t) := Finset.sum_congr rfl (fun t _ => hterm t)
    _ = g • ∑ t ∈ T, coindSummand U f (g⁻¹ * t) := by rw [Finset.smul_sum]
    _ = g • ∑ t ∈ T, coindSummand U f t := by rw [hinner]
    _ = g • coindAvgSum U T f := rfl

/-- The averaging sum of the diagonal is `[G:U] • m`. -/
theorem coindAvgSum_diag (U : Subgroup G) [Finite (G ⧸ U)] {T : Finset G}
    (hT : IsCosetReps U T) (diag : M →+ Work.SSGRoute.PT.Coind G U M)
    (hdiag : ∀ (m : M) (x : G), (diag m : G → M) x = x⁻¹ • m) (m : M) :
    coindAvgSum U T (diag m) = (U.index : ℕ) • m := by
  rw [coindAvgSum_apply]
  have hterm : ∀ t : G, coindSummand U (diag m) t = m := by
    intro t
    rw [coindSummand, hdiag, smul_smul, mul_inv_cancel, one_smul]
  calc (∑ t ∈ T, coindSummand U (diag m) t) = ∑ t ∈ T, m :=
        Finset.sum_congr rfl (fun t _ => hterm t)
    _ = (T.card : ℕ) • m := by simp
    _ = (U.index : ℕ) • m := by rw [card_eq_index_of_isCosetReps U hT]

/-- The diagonal `m ↦ (x ↦ x⁻¹ • m)` as an additive map into the coinduced module. -/
noncomputable def coindDiag (U : Subgroup G) : M →+ Work.SSGRoute.PT.Coind G U M :=
  { toFun := fun m => ⟨fun x => x⁻¹ • m, by
      intro x u
      show (x * (u : G))⁻¹ • m = ((u⁻¹ : U) : G) • (x⁻¹ • m)
      rw [mul_inv_rev, mul_smul]
      rfl⟩
    map_zero' := by
      refine Subtype.ext ?_
      funext x
      simp
    map_add' := fun a b => by
      refine Subtype.ext ?_
      funext x
      simp [smul_add] }

theorem coindDiag_apply (U : Subgroup G) (m : M) (x : G) :
    (coindDiag U m : G → M) x = x⁻¹ • m := rfl

/-- The diagonal is `G`-equivariant. -/
theorem coindDiag_eqv (U : Subgroup G) :
    Work.GroupCohomology.IsEquivariant G (coindDiag (G := G) (M := M) U) := by
  intro g m
  refine Subtype.ext ?_
  funext x
  show (coindDiag U (g • m) : G → M) x = ((g • coindDiag U m : Work.SSGRoute.PT.Coind G U M) : G → M) x
  rw [coindDiag_apply, Work.SSGRoute.PT.Coind.smul_apply, coindDiag_apply, mul_inv_rev,
    inv_inv, mul_smul]

end Summand

section Main

variable {G : Type*} [Group G] [TopologicalSpace G]

theorem h3CoprimeIndex (p : ℕ) [Fact p.Prime] (U : Subgroup G) [U.FiniteIndex]
    (hcop : Nat.Coprime U.index p)
    {M : Type*} [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M]
    [SMulCommClass G (ZMod p) M] [Finite M]
    (hsh : Nonempty (Work.SSGRoute.H3 (M := Work.SSGRoute.PT.Coind G U M) G ≃+
      Work.SSGRoute.H3 (M := M) U))
    (h : Subsingleton (Work.SSGRoute.H3 (M := M) U)) :
    Subsingleton (Work.SSGRoute.H3 (M := M) G) := by
  classical
  obtain ⟨T, hT⟩ := exists_isCosetReps_of_finiteIndex U
  -- the inverse of the index, as a unit of `𝔽_p` (this is exactly `Nat.Coprime U.index p`)
  let u : (ZMod p)ˣ := ZMod.unitOfCoprime U.index hcop
  let c : ZMod p := (u⁻¹ : (ZMod p)ˣ)
  have hu : (u : ZMod p) = (U.index : ZMod p) := ZMod.coe_unitOfCoprime U.index hcop
  have hc : c * (U.index : ZMod p) = 1 := by
    have hcu : c * (u : ZMod p) = 1 := by
      dsimp only [c]
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rwa [hu] at hcu
  -- the averaging, rescaled by the inverse of the index
  let avg : Work.SSGRoute.PT.Coind G U M →+ M :=
    { toFun := fun f => c • coindAvgSum U T f
      map_zero' := by simp
      map_add' := fun f g => by rw [map_add, smul_add] }
  have avg_apply : ∀ f, avg f = c • coindAvgSum U T f := fun _ => rfl
  have avg_eqv : Work.GroupCohomology.IsEquivariant G avg := by
    intro g f
    rw [avg_apply, avg_apply, coindAvgSum_smul U hT g f, smul_comm g c (coindAvgSum U T f)]
  have avg_diag : ∀ m : M, avg (coindDiag (M := M) U m) = m := by
    intro m
    rw [avg_apply, coindAvgSum_diag U hT (coindDiag (M := M) U) (coindDiag_apply U) m,
      ← Nat.cast_smul_eq_nsmul (ZMod p) U.index m, smul_smul, hc, one_smul]
  -- `avg` retracts the diagonal, already at the level of cochains: the composite
  -- `H³(avg) ∘ H³(diag)` acts pointwise as `m ↦ avg (diag m) = m`
  have hretr : ∀ x : Work.SSGRoute.H3 (M := M) G,
      Work.SSGRoute.H3Map.mapH3 avg avg_eqv
        (Work.SSGRoute.H3Map.mapH3 (coindDiag (M := M) U) (coindDiag_eqv (M := M) U) x) = x := by
    intro x
    refine Work.SSGRoute.H3_induction_on
      (C := fun w => Work.SSGRoute.H3Map.mapH3 avg avg_eqv
        (Work.SSGRoute.H3Map.mapH3 (coindDiag (M := M) U) (coindDiag_eqv (M := M) U) w) = w)
      x (fun cc => ?_)
    have hpoint : ∀ q : G × G × G,
        (Work.SSGRoute.H3Map.mapZ3 avg avg_eqv
          (Work.SSGRoute.H3Map.mapZ3 (coindDiag (M := M) U) (coindDiag_eqv (M := M) U) cc)
            : G × G × G → M) q = (cc : G × G × G → M) q := by
      intro q
      rw [Work.SSGRoute.H3Map.mapZ3_apply, Work.SSGRoute.H3Map.mapZ3_apply]
      exact avg_diag ((cc : G × G × G → M) q)
    have hz : Work.SSGRoute.H3Map.mapZ3 avg avg_eqv
        (Work.SSGRoute.H3Map.mapZ3 (coindDiag (M := M) U) (coindDiag_eqv (M := M) U) cc) = cc :=
      Subtype.ext (funext hpoint)
    rw [Work.SSGRoute.H3Map.mapH3_H3π (coindDiag (M := M) U) (coindDiag_eqv (M := M) U) cc,
      Work.SSGRoute.H3Map.mapH3_H3π avg avg_eqv
        (Work.SSGRoute.H3Map.mapZ3 (coindDiag (M := M) U) (coindDiag_eqv (M := M) U) cc), hz]
  have hinj : Function.Injective
      (Work.SSGRoute.H3Map.mapH3 (coindDiag (M := M) U) (coindDiag_eqv (M := M) U)) := by
    intro x y hxy
    calc x = Work.SSGRoute.H3Map.mapH3 avg avg_eqv
          (Work.SSGRoute.H3Map.mapH3 (coindDiag (M := M) U) (coindDiag_eqv (M := M) U) x) := (hretr x).symm
      _ = Work.SSGRoute.H3Map.mapH3 avg avg_eqv
          (Work.SSGRoute.H3Map.mapH3 (coindDiag (M := M) U) (coindDiag_eqv (M := M) U) y) := by rw [hxy]
      _ = y := hretr y
  obtain ⟨e⟩ := hsh
  haveI : Subsingleton (Work.SSGRoute.H3 (M := Work.SSGRoute.PT.Coind G U M) G) :=
    ⟨fun a b => e.injective (h.elim (e a) (e b))⟩
  exact ⟨fun a b => hinj (Subsingleton.elim _ _)⟩

end Main

end Work.SSGRoute.EulerSymm
