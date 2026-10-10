import Mathlib.GroupTheory.Nilpotent
import Mathlib.Algebra.Field.ZMod
import Mathlib.Topology.Defs.Basic
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The spaces on which the local pairing descends

Vocabulary for the "surjectivity half of the perfectness of the local pairing"
(`Work.SSGRoute.PT.localPairing_surjective_dual`).

For a subgroup `H ≤ Γ`, a group `G` acting on the `ZMod p`-module `M` (the action of `Γ` going
through `act : Γ →* G`), we single out the `ZMod p`-submodules of the function space `Γ → M`:

* `cocycleSub act H`   : the `1`-cocycles on `H`;
* `locConstSub H`      : the locally constant functions on `H`;
* `cobSub act H`       : the coboundaries on `H`;
* `cocycleLocConst`    : cocycles which are locally constant (the domain of the pairing);
* `cobInDomain`        : the coboundaries inside that domain (killed by the pairing);
* `cobInDomainOf`      : the same, as a submodule of `cocycleLocConst`, so that the quotient
  `cocycleLocConst ⧸ cobInDomainOf` is available.

Note that all of `SSGRoute.IsCocycleOn`, `SSGRoute.IsLocConstOn`, `SSGRoute.IsCoboundaryOn` only
constrain the values on `H`, so these are *not* the naive submodules of the full function space;
in particular `cobSub` is strictly larger than the range of the coboundary map `cobMap`.
-/

namespace Work.SSGRoute.PT

set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

variable {p : ℕ}

/-- The `ZMod p`-submodule of `1`-cocycles on `H`. -/
def cocycleSub {Γ G M : Type} [Group Γ] [Group G] [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction G M] [SMulCommClass G (ZMod p) M]
    (act : Γ →* G) (H : Subgroup Γ) : Submodule (ZMod p) (Γ → M) where
  carrier := {f | SSGRoute.IsCocycleOn act H f}
  zero_mem' := by intro g _ h _; simp
  add_mem' := by
    intro f f' hf hf' g hg h hh
    have h1 : f (g * h) = f g + act g • f h := hf g hg h hh
    have h2 : f' (g * h) = f' g + act g • f' h := hf' g hg h hh
    simp only [Pi.add_apply]
    rw [h1, h2, smul_add]
    abel
  smul_mem' := by
    intro c f hf g hg h hh
    have h1 : f (g * h) = f g + act g • f h := hf g hg h hh
    simp only [Pi.smul_apply]
    rw [h1, smul_add]
    congr 1
    exact (smul_comm (act g) c (f h)).symm

/-- The `ZMod p`-submodule of functions on `Γ` which are locally constant on `H`. -/
def locConstSub {Γ M : Type} [Group Γ] [TopologicalSpace Γ] [AddCommGroup M]
    [Module (ZMod p) M] (H : Subgroup Γ) : Submodule (ZMod p) (Γ → M) where
  carrier := {f | SSGRoute.IsLocConstOn H f}
  zero_mem' := by
    refine ⟨⊤, ?_, ?_⟩
    · simp
    · intro g _ u _ _; simp
  add_mem' := by
    intro f f' hf hf'
    obtain ⟨U, hUo, hU⟩ := hf
    obtain ⟨U', hUo', hU'⟩ := hf'
    refine ⟨U ⊓ U', ?_, ?_⟩
    · rw [Subgroup.coe_inf]; exact hUo.inter hUo'
    · intro g hg u hu huH
      rw [Subgroup.mem_inf] at hu
      simp only [Pi.add_apply]
      rw [hU g hg u hu.1 huH, hU' g hg u hu.2 huH]
  smul_mem' := by
    intro c f hf
    obtain ⟨U, hUo, hU⟩ := hf
    refine ⟨U, hUo, ?_⟩
    intro g hg u hu huH
    simp only [Pi.smul_apply]
    rw [hU g hg u hu huH]

/-- The `ZMod p`-submodule of coboundaries on `H` (functions `g ↦ act g • m - m` *on `H`*). -/
def cobSub {Γ G M : Type} [Group Γ] [Group G] [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction G M] [SMulCommClass G (ZMod p) M]
    (act : Γ →* G) (H : Subgroup Γ) : Submodule (ZMod p) (Γ → M) where
  carrier := {f | SSGRoute.IsCoboundaryOn act H f}
  zero_mem' := by
    refine ⟨0, fun g _ => ?_⟩
    simp
  add_mem' := by
    intro f f' hf hf'
    obtain ⟨m, hm⟩ := hf
    obtain ⟨m', hm'⟩ := hf'
    refine ⟨m + m', fun g hg => ?_⟩
    simp only [Pi.add_apply]
    rw [hm g hg, hm' g hg, smul_add]
    abel
  smul_mem' := by
    intro c f hf
    obtain ⟨m, hm⟩ := hf
    refine ⟨c • m, fun g hg => ?_⟩
    simp only [Pi.smul_apply]
    rw [hm g hg, smul_sub, smul_comm (act g) c m]

@[simp] theorem mem_cocycleSub {Γ G M : Type} [Group Γ] [Group G] [AddCommGroup M]
    [Module (ZMod p) M] [DistribMulAction G M] [SMulCommClass G (ZMod p) M]
    (act : Γ →* G) (H : Subgroup Γ) (f : Γ → M) :
    f ∈ cocycleSub (p := p) act H ↔ SSGRoute.IsCocycleOn act H f := Iff.rfl

@[simp] theorem mem_locConstSub {Γ M : Type} [Group Γ] [TopologicalSpace Γ] [AddCommGroup M]
    [Module (ZMod p) M] (H : Subgroup Γ) (f : Γ → M) :
    f ∈ locConstSub (p := p) H ↔ SSGRoute.IsLocConstOn H f := Iff.rfl

@[simp] theorem mem_cobSub {Γ G M : Type} [Group Γ] [Group G] [AddCommGroup M]
    [Module (ZMod p) M] [DistribMulAction G M] [SMulCommClass G (ZMod p) M]
    (act : Γ →* G) (H : Subgroup Γ) (f : Γ → M) :
    f ∈ cobSub (p := p) act H ↔ SSGRoute.IsCoboundaryOn act H f := Iff.rfl

/-- The domain of the local pairing: functions which are both a cocycle and locally constant. -/
def cocycleLocConst {Γ G M : Type} [Group Γ] [TopologicalSpace Γ] [Group G] [AddCommGroup M]
    [Module (ZMod p) M] [DistribMulAction G M] [SMulCommClass G (ZMod p) M]
    (act : Γ →* G) (H : Subgroup Γ) : Submodule (ZMod p) (Γ → M) :=
  cocycleSub act H ⊓ locConstSub (p := p) H

/-- The coboundaries inside the domain of the local pairing. -/
def cobInDomain {Γ G M : Type} [Group Γ] [TopologicalSpace Γ] [Group G] [AddCommGroup M]
    [Module (ZMod p) M] [DistribMulAction G M] [SMulCommClass G (ZMod p) M]
    (act : Γ →* G) (H : Subgroup Γ) : Submodule (ZMod p) (Γ → M) :=
  cocycleLocConst (p := p) act H ⊓ cobSub act H

/-- `cobInDomain`, viewed as a submodule of `cocycleLocConst` (so that the quotient type of the
local pairing is `cocycleLocConst ⧸ cobInDomainOf`). -/
def cobInDomainOf {Γ G M : Type} [Group Γ] [TopologicalSpace Γ] [Group G] [AddCommGroup M]
    [Module (ZMod p) M] [DistribMulAction G M] [SMulCommClass G (ZMod p) M]
    (act : Γ →* G) (H : Subgroup Γ) :
    Submodule (ZMod p) (cocycleLocConst (p := p) (M := M) act H) :=
  Submodule.comap (cocycleLocConst (p := p) (M := M) act H).subtype
    (cobInDomain (p := p) (M := M) act H)

@[simp] theorem mem_cocycleLocConst {Γ G M : Type} [Group Γ] [TopologicalSpace Γ] [Group G]
    [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M] [SMulCommClass G (ZMod p) M]
    (act : Γ →* G) (H : Subgroup Γ) (f : Γ → M) :
    f ∈ cocycleLocConst (p := p) (M := M) act H ↔
      SSGRoute.IsCocycleOn act H f ∧ SSGRoute.IsLocConstOn H f := by
  simp [cocycleLocConst]

@[simp] theorem mem_cobInDomain {Γ G M : Type} [Group Γ] [TopologicalSpace Γ] [Group G]
    [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M] [SMulCommClass G (ZMod p) M]
    (act : Γ →* G) (H : Subgroup Γ) (f : Γ → M) :
    f ∈ cobInDomain (p := p) (M := M) act H ↔
      (SSGRoute.IsCocycleOn act H f ∧ SSGRoute.IsLocConstOn H f) ∧
        SSGRoute.IsCoboundaryOn act H f := by
  simp [cobInDomain]

@[simp] theorem mem_cobInDomainOf {Γ G M : Type} [Group Γ] [TopologicalSpace Γ] [Group G]
    [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M] [SMulCommClass G (ZMod p) M]
    (act : Γ →* G) (H : Subgroup Γ) (f : cocycleLocConst (p := p) (M := M) act H) :
    f ∈ cobInDomainOf (p := p) (M := M) act H ↔ SSGRoute.IsCoboundaryOn act H f.1 := by
  simp [cobInDomainOf, cobInDomain]

/-- The coboundary map `m ↦ (g ↦ act g • m - m)`. -/
def cobMap {Γ G M : Type} [Group Γ] [Group G] [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction G M] [SMulCommClass G (ZMod p) M] (act : Γ →* G) : M →ₗ[ZMod p] (Γ → M) where
  toFun m := fun g => act g • m - m
  map_add' m m' := by
    ext g
    simp only [Pi.add_apply, Pi.sub_apply, smul_add]
    abel
  map_smul' c m := by
    ext g
    simp only [Pi.smul_apply, Pi.sub_apply, RingHom.id_apply, smul_sub]
    rw [smul_comm (act g) c m]

/-- **An additive map into `ZMod p` is `ZMod p`-linear.** -/
theorem zmod_smul_of_additive {p : ℕ} [Fact p.Prime] {S : Type} [AddCommGroup S]
    [Module (ZMod p) S] (F : S → ZMod p) (hF : ∀ x y : S, F (x + y) = F x + F y)
    (c : ZMod p) (x : S) : F (c • x) = c • F x := by
  have hF0 : F 0 = 0 := by
    have h : F 0 = F 0 + F 0 := by simpa [zero_add] using hF 0 0
    exact add_left_cancel (show F 0 + F 0 = F 0 + 0 by rw [add_zero]; exact h.symm)
  have hnat : ∀ n : ℕ, F (n • x) = n • F x := by
    intro n
    induction n with
    | zero => rw [zero_nsmul, hF0, zero_nsmul]
    | succ k ih => rw [succ_nsmul, hF, ih, succ_nsmul]
  have h1 : c • x = (c.val : ℕ) • x := by
    conv_lhs => rw [← ZMod.natCast_zmod_val c]
    exact Nat.cast_smul_eq_nsmul (ZMod p) c.val x
  have h2 : c • F x = (c.val : ℕ) • F x := by
    conv_lhs => rw [← ZMod.natCast_zmod_val c]
    exact Nat.cast_smul_eq_nsmul (ZMod p) c.val (F x)
  rw [h1, hnat, ← h2]

/-- An additive map into `ZMod p` packaged as a linear map. -/
def linearMapOfAdditive {p : ℕ} [Fact p.Prime] {S : Type} [AddCommGroup S]
    [Module (ZMod p) S] (F : S → ZMod p) (hF : ∀ x y : S, F (x + y) = F x + F y) :
    S →ₗ[ZMod p] ZMod p where
  toFun := F
  map_add' := hF
  map_smul' := fun c x => zmod_smul_of_additive F hF c x

end Work.SSGRoute.PT
