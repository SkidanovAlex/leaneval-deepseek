import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.PT.LocalPairingSpaces
import Submission.Work.SSGRoute.PT.pt_localPairingDual
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The surjectivity half of the perfectness of the local pairing

This file contains the general form of `Work.SSGRoute.PT.localPairing_surjective_dual`: for an
abstract pair of `ZMod p`-modules `M`, `N` with an action of a group `Γ` through `act : Γ →* G`,
a pairing `pair` which is additive in each variable on locally constant `1`-cocycles and kills
coboundaries, and whose two induced forms on `X = cocycleLocConst_M / cobInDomainOf` and
`Y = cocycleLocConst_N / cobInDomainOf` are non-degenerate, every linear functional `lam` on the
locally constant `1`-cocycles with values in `N` which is additive on cocycles and kills
coboundaries is represented by a locally constant `M`-cocycle.

The proof is a dimension count: `hfinA`/`hfinB` make `X` and `Y` finite, `pair` descends to
`β3 : Y →ₗ X →ₗ ZMod p`, its non-degeneracy makes it a perfect pairing, and
`PT.pt_localPairingDual` realises `lam` as `β3 · x₀`.
-/

namespace Work.SSGRoute.PT

set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

/-- **Finiteness of the space of locally constant `1`-cocycles modulo coboundaries.**  If the
locally constant `1`-cocycles `a : Γ → M` are, modulo coboundaries, `ZMod p`-linear combinations of
`n` fixed functions `φ i`, then the quotient `cocycleLocConst ⧸ cobInDomainOf` on which the local
pairing descends is finite. -/
theorem aux_finite_quot {p : ℕ} [Fact p.Prime]
    {Γ G M : Type} [Group Γ] [TopologicalSpace Γ] [Group G] [AddCommGroup M]
    [Module (ZMod p) M] [DistribMulAction G M] [SMulCommClass G (ZMod p) M]
    (act : Γ →* G) (H : Subgroup Γ)
    (hfin : ∃ (n : ℕ) (φ : Fin n → Γ → M),
      ∀ a : Γ → M, SSGRoute.IsCocycleOn act H a → SSGRoute.IsLocConstOn H a →
        ∃ (c : Fin n → ZMod p) (z : Γ → M),
          SSGRoute.IsCoboundaryOn act H z ∧ a = (∑ i, c i • φ i) + z) :
    Finite ((cocycleLocConst (p := p) (M := M) act H) ⧸
      (cobInDomainOf (p := p) (M := M) act H)) := by
  classical
  obtain ⟨n, φ, hφ⟩ := hfin
  let W : Submodule (ZMod p) (Γ → M) := cocycleLocConst (p := p) (M := M) act H
  let C : Submodule (ZMod p) (Γ → M) := cobSub (p := p) act H
  let S : Submodule (ZMod p) W := cobInDomainOf (p := p) (M := M) act H
  have hca : ∀ x : W, SSGRoute.IsCocycleOn act H x.1 ∧ SSGRoute.IsLocConstOn H x.1 :=
    fun x => (mem_cocycleLocConst (p := p) act H x.1).mp x.2
  have hmemC : ∀ x : W, (Submodule.mkQ C) x.1 = (0 : (Γ → M) ⧸ C) ↔ x ∈ S := by
    intro x
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact (mem_cobSub (p := p) act H x.1).trans (mem_cobInDomainOf (p := p) act H x).symm
  let Ψ : W →ₗ[ZMod p] ((Γ → M) ⧸ C) := (Submodule.mkQ C).comp W.subtype
  have hΨ : ∀ x : W, Ψ x = (Submodule.mkQ C) x.1 := fun x => rfl
  have hS_le_ker : S ≤ Ψ.ker := by
    intro x hx
    rw [LinearMap.mem_ker, hΨ x]
    exact (hmemC x).mpr hx
  let ιlin : (W ⧸ S) →ₗ[ZMod p] ((Γ → M) ⧸ C) := Submodule.liftQ S Ψ hS_le_ker
  have hιlin : ∀ x : W, ιlin (Submodule.Quotient.mk x) = (Submodule.mkQ C) x.1 := by
    intro x
    rw [show ιlin (Submodule.Quotient.mk x) = Ψ x from
      Submodule.liftQ_apply S Ψ (h := hS_le_ker) x, hΨ x]
  let ψ : Fin n → ((Γ → M) ⧸ C) := fun i => (Submodule.mkQ C) (φ i)
  let V : Submodule (ZMod p) ((Γ → M) ⧸ C) := Submodule.span (ZMod p) (Set.range ψ)
  haveI hVfin : Module.Finite (ZMod p) V :=
    Module.Finite.of_fg (Submodule.fg_span (Set.finite_range ψ))
  haveI hVfin2 : Finite V := Work.Shrinking.finite_of_moduleFinite (p := p) (M := V)
  have hmemV : ∀ z : W ⧸ S, ιlin z ∈ V := by
    intro z
    refine Submodule.Quotient.induction_on S z (fun x => ?_)
    rw [hιlin x]
    obtain ⟨c, z', hz', hx⟩ := hφ x.1 (hca x).1 (hca x).2
    have hz0 : (Submodule.mkQ C) z' = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact (mem_cobSub (p := p) act H z').mpr hz'
    have hsum : (Submodule.mkQ C) (∑ i, c i • φ i) = ∑ i, c i • (Submodule.mkQ C) (φ i) := by
      rw [map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      exact map_smul (Submodule.mkQ C) (c i) (φ i)
    have hx' : (Submodule.mkQ C) x.1 = ∑ i, c i • ψ i := by
      rw [hx, map_add, hz0, add_zero]
      exact hsum
    rw [hx']
    exact Submodule.sum_mem V (fun i _ =>
      Submodule.smul_mem V (c i) (Submodule.subset_span (Set.mem_range_self i)))
  have hzero : ∀ z : W ⧸ S, ιlin z = 0 → z = 0 := by
    intro z
    refine Submodule.Quotient.induction_on S z (fun x => ?_)
    intro hz
    rw [Submodule.Quotient.mk_eq_zero]
    have hιx : ιlin (Submodule.Quotient.mk x) = (Submodule.mkQ C) x.1 := by
      rw [show ιlin (Submodule.Quotient.mk x) = Ψ x from
        Submodule.liftQ_apply S Ψ (h := hS_le_ker) x, hΨ x]
    rw [hιx] at hz
    exact (hmemC x).mp hz
  refine Finite.of_injective (fun z : W ⧸ S => (⟨ιlin z, hmemV z⟩ : V)) ?_
  intro z z' h
  have h2 : ιlin z = ιlin z' := congrArg Subtype.val h
  have h3 : z - z' = 0 := by
    refine hzero (z - z') ?_
    rw [map_sub, h2, sub_self]
  exact sub_eq_zero.mp h3

/-- **Descent of a functional to the quotient.**  A function `lam` on `Γ → N` which is additive on
`1`-cocycles and vanishes on coboundaries defines a `ZMod p`-linear functional on
`cocycleLocConst ⧸ cobInDomainOf`, whose value on (the class of) a locally constant cocycle `b` is
`lam b`. -/
theorem aux_descend_functional {p : ℕ} [Fact p.Prime]
    {Γ G N : Type} [Group Γ] [TopologicalSpace Γ] [Group G] [AddCommGroup N]
    [Module (ZMod p) N] [DistribMulAction G N] [SMulCommClass G (ZMod p) N]
    (act : Γ →* G) (H : Subgroup Γ) (lam : (Γ → N) → ZMod p)
    (hadd : ∀ b b' : Γ → N, SSGRoute.IsCocycleOn act H b → SSGRoute.IsCocycleOn act H b' →
      lam (b + b') = lam b + lam b')
    (hcob : ∀ b : Γ → N, SSGRoute.IsCoboundaryOn act H b → lam b = 0) :
    ∃ Λ : ((cocycleLocConst (p := p) (M := N) act H) ⧸
        (cobInDomainOf (p := p) (M := N) act H)) →ₗ[ZMod p] ZMod p,
      ∀ b : cocycleLocConst (p := p) (M := N) act H,
        Λ (Submodule.Quotient.mk b) = lam b.1 := by
  classical
  let W : Submodule (ZMod p) (Γ → N) := cocycleLocConst (p := p) (M := N) act H
  let S : Submodule (ZMod p) W := cobInDomainOf (p := p) (M := N) act H
  have hcn : ∀ b : W, SSGRoute.IsCocycleOn act H b.1 :=
    fun b => ((mem_cocycleLocConst (p := p) act H b.1).mp b.2).1
  have hFadd : ∀ b b' : W, (fun b : W => lam b.1) (b + b') = (fun b : W => lam b.1) b +
      (fun b : W => lam b.1) b' := by
    intro b b'
    change lam (b + b').1 = lam b.1 + lam b'.1
    rw [Submodule.coe_add]
    exact hadd b.1 b'.1 (hcn b) (hcn b')
  let F : W →ₗ[ZMod p] ZMod p := linearMapOfAdditive (fun b : W => lam b.1) hFadd
  have hF : ∀ b : W, F b = lam b.1 := fun b => rfl
  have hker : S ≤ F.ker := by
    intro b hb
    rw [LinearMap.mem_ker, hF]
    exact hcob b.1 ((mem_cobInDomainOf (p := p) act H b).mp hb)
  refine ⟨Submodule.liftQ S F hker, fun b => ?_⟩
  rw [show (Submodule.liftQ S F hker) (Submodule.Quotient.mk b) = F b from
    Submodule.liftQ_apply S F (h := hker) b, hF]

/-- **The general form of the surjectivity half of the perfectness of the local pairing.** -/
theorem pairing_surjective_dual_general {p : ℕ} [Fact p.Prime]
    {Γ G M N : Type} [Group Γ] [TopologicalSpace Γ] [Group G]
    [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction G M] [SMulCommClass G (ZMod p) M]
    [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction G N] [SMulCommClass G (ZMod p) N]
    (act : Γ →* G) (H : Subgroup Γ) (pair : (Γ → M) → (Γ → N) → ZMod p)
    (hadd_left : ∀ (a a' : Γ → M) (b : Γ → N),
      SSGRoute.IsCocycleOn act H a → SSGRoute.IsLocConstOn H a →
      SSGRoute.IsCocycleOn act H a' → SSGRoute.IsLocConstOn H a' →
      SSGRoute.IsCocycleOn act H b → SSGRoute.IsLocConstOn H b →
      pair (a + a') b = pair a b + pair a' b)
    (hadd_right : ∀ (a : Γ → M) (b b' : Γ → N),
      SSGRoute.IsCocycleOn act H a → SSGRoute.IsLocConstOn H a →
      SSGRoute.IsCocycleOn act H b → SSGRoute.IsLocConstOn H b →
      SSGRoute.IsCocycleOn act H b' → SSGRoute.IsLocConstOn H b' →
      pair a (b + b') = pair a b + pair a b')
    (hcob_pair : ∀ (a : Γ → M) (b : Γ → N),
      SSGRoute.IsCocycleOn act H a → SSGRoute.IsLocConstOn H a →
      SSGRoute.IsCocycleOn act H b → SSGRoute.IsLocConstOn H b →
      (SSGRoute.IsCoboundaryOn act H a ∨ SSGRoute.IsCoboundaryOn act H b) →
      pair a b = 0)
    (hperf_left : ∀ a : Γ → M,
      SSGRoute.IsCocycleOn act H a → SSGRoute.IsLocConstOn H a →
      (∀ b : Γ → N, SSGRoute.IsCocycleOn act H b → SSGRoute.IsLocConstOn H b →
        pair a b = 0) →
      SSGRoute.IsCoboundaryOn act H a)
    (hperf_right : ∀ b : Γ → N,
      SSGRoute.IsCocycleOn act H b → SSGRoute.IsLocConstOn H b →
      (∀ a : Γ → M, SSGRoute.IsCocycleOn act H a → SSGRoute.IsLocConstOn H a →
        pair a b = 0) →
      SSGRoute.IsCoboundaryOn act H b)
    (hfinA : ∃ (n : ℕ) (φ : Fin n → Γ → M),
      ∀ a : Γ → M, SSGRoute.IsCocycleOn act H a → SSGRoute.IsLocConstOn H a →
        ∃ (c : Fin n → ZMod p) (z : Γ → M),
          SSGRoute.IsCoboundaryOn act H z ∧ a = (∑ i, c i • φ i) + z)
    (hfinB : ∃ (n : ℕ) (ψ : Fin n → Γ → N),
      ∀ b : Γ → N, SSGRoute.IsCocycleOn act H b → SSGRoute.IsLocConstOn H b →
        ∃ (c : Fin n → ZMod p) (z : Γ → N),
          SSGRoute.IsCoboundaryOn act H z ∧ b = (∑ i, c i • ψ i) + z)
    (lam : (Γ → N) → ZMod p)
    (hadd : ∀ b b' : Γ → N, SSGRoute.IsCocycleOn act H b → SSGRoute.IsCocycleOn act H b' →
      lam (b + b') = lam b + lam b')
    (hcob : ∀ b : Γ → N, SSGRoute.IsCoboundaryOn act H b → lam b = 0) :
    ∃ a : Γ → M, SSGRoute.IsCocycleOn act H a ∧ SSGRoute.IsLocConstOn H a ∧
      ∀ b : Γ → N, SSGRoute.IsCocycleOn act H b → SSGRoute.IsLocConstOn H b →
        pair a b = lam b := by
  classical
  let WM : Submodule (ZMod p) (Γ → M) := cocycleLocConst (p := p) (M := M) act H
  let WN : Submodule (ZMod p) (Γ → N) := cocycleLocConst (p := p) (M := N) act H
  let SM : Submodule (ZMod p) WM := cobInDomainOf (p := p) (M := M) act H
  let SN : Submodule (ZMod p) WN := cobInDomainOf (p := p) (M := N) act H
  have hca : ∀ a : WM, SSGRoute.IsCocycleOn act H a.1 ∧ SSGRoute.IsLocConstOn H a.1 :=
    fun a => (mem_cocycleLocConst (p := p) act H a.1).mp a.2
  have hcn : ∀ b : WN, SSGRoute.IsCocycleOn act H b.1 ∧ SSGRoute.IsLocConstOn H b.1 :=
    fun b => (mem_cocycleLocConst (p := p) act H b.1).mp b.2
  have hsM : ∀ a : WM, a ∈ SM ↔ SSGRoute.IsCoboundaryOn act H a.1 :=
    fun a => mem_cobInDomainOf (p := p) act H a
  have hsN : ∀ b : WN, b ∈ SN ↔ SSGRoute.IsCoboundaryOn act H b.1 :=
    fun b => mem_cobInDomainOf (p := p) act H b
  -- additivity of the pairing on the two submodules
  have hinner : ∀ a : WM, ∀ b b' : WN, pair a.1 (b + b').1 = pair a.1 b.1 + pair a.1 b'.1 := by
    intro a b b'
    rw [Submodule.coe_add]
    exact hadd_right a.1 b.1 b'.1 (hca a).1 (hca a).2 (hcn b).1 (hcn b).2 (hcn b').1 (hcn b').2
  have houter : ∀ a a' : WM, ∀ b : WN, pair (a + a').1 b.1 = pair a.1 b.1 + pair a'.1 b.1 := by
    intro a a' b
    rw [Submodule.coe_add]
    exact hadd_left a.1 a'.1 b.1 (hca a).1 (hca a).2 (hca a').1 (hca a').2 (hcn b).1 (hcn b).2
  -- the form β0 : WM →ₗ WN →ₗ ZMod p
  let β0 : WM →ₗ[ZMod p] (WN →ₗ[ZMod p] ZMod p) :=
    { toFun := fun a =>
        { toFun := fun b => pair a.1 b.1
          map_add' := fun b b' => hinner a b b'
          map_smul' := fun c b =>
            zmod_smul_of_additive (fun b : WN => pair a.1 b.1) (fun b b' => hinner a b b') c b }
      map_add' := fun a a' => by
        ext b
        exact houter a a' b
      map_smul' := fun c a => by
        ext b
        exact zmod_smul_of_additive (fun a : WM => pair a.1 b.1) (fun a a' => houter a a' b) c a }
  -- descend the first variable
  have hker0 : SM ≤ β0.ker := by
    intro x hx
    rw [LinearMap.mem_ker]
    ext b
    exact hcob_pair x.1 b.1 (hca x).1 (hca x).2 (hcn b).1 (hcn b).2 (Or.inl ((hsM x).mp hx))
  let β1 : (WM ⧸ SM) →ₗ[ZMod p] (WN →ₗ[ZMod p] ZMod p) := Submodule.liftQ SM β0 hker0
  have hβ1 : ∀ (a : WM) (b : WN), β1 (Submodule.Quotient.mk a) b = pair a.1 b.1 := by
    intro a b
    rw [show β1 (Submodule.Quotient.mk a) = β0 a from
      Submodule.liftQ_apply SM β0 (h := hker0) a]
    rfl
  -- descend the second variable
  let β2 : WN →ₗ[ZMod p] ((WM ⧸ SM) →ₗ[ZMod p] ZMod p) := β1.flip
  have hβ2 : ∀ (a : WM) (b : WN), β2 b (Submodule.Quotient.mk a) = pair a.1 b.1 := by
    intro a b
    change (β1.flip b) (Submodule.Quotient.mk a) = pair a.1 b.1
    rw [LinearMap.flip_apply, hβ1]
  have hker2 : SN ≤ β2.ker := by
    intro y hy
    rw [LinearMap.mem_ker]
    apply LinearMap.ext
    intro x
    refine Submodule.Quotient.induction_on SM x (fun a => ?_)
    rw [hβ2 a y]
    exact hcob_pair a.1 y.1 (hca a).1 (hca a).2 (hcn y).1 (hcn y).2
      (Or.inr ((hsN y).mp hy))
  let β3 : (WN ⧸ SN) →ₗ[ZMod p] ((WM ⧸ SM) →ₗ[ZMod p] ZMod p) := Submodule.liftQ SN β2 hker2
  have hβ3 : ∀ (a : WM) (b : WN),
      β3 (Submodule.Quotient.mk b) (Submodule.Quotient.mk a) = pair a.1 b.1 := by
    intro a b
    rw [show β3 (Submodule.Quotient.mk b) = β2 b from
      Submodule.liftQ_apply SN β2 (h := hker2) b, hβ2]
  -- non-degeneracy
  have hnondegL : ∀ y : (WN ⧸ SN), (∀ x : (WM ⧸ SM), β3 y x = 0) → y = 0 := by
    intro y
    refine Submodule.Quotient.induction_on SN y (fun b => ?_)
    intro hy
    rw [Submodule.Quotient.mk_eq_zero]
    refine (hsN b).mpr (hperf_right b.1 (hcn b).1 (hcn b).2 (fun a ha ha' => ?_))
    have hh := hy (Submodule.Quotient.mk (⟨a, (mem_cocycleLocConst (p := p) act H a).mpr
      ⟨ha, ha'⟩⟩ : WM))
    rw [hβ3 (⟨a, (mem_cocycleLocConst (p := p) act H a).mpr ⟨ha, ha'⟩⟩ : WM) b] at hh
    exact hh
  have hnondegR : ∀ x : (WM ⧸ SM), (∀ y : (WN ⧸ SN), β3 y x = 0) → x = 0 := by
    intro x
    refine Submodule.Quotient.induction_on SM x (fun a => ?_)
    intro hx
    rw [Submodule.Quotient.mk_eq_zero]
    refine (hsM a).mpr (hperf_left a.1 (hca a).1 (hca a).2 (fun b hb hb' => ?_))
    have hh := hx (Submodule.Quotient.mk (⟨b, (mem_cocycleLocConst (p := p) act H b).mpr
      ⟨hb, hb'⟩⟩ : WN))
    rw [hβ3 a (⟨b, (mem_cocycleLocConst (p := p) act H b).mpr ⟨hb, hb'⟩⟩ : WN)] at hh
    exact hh
  -- finiteness
  haveI hfinX : Finite (WN ⧸ SN) := aux_finite_quot (p := p) (M := N) act H hfinB
  haveI hfinY : Finite (WM ⧸ SM) := aux_finite_quot (p := p) (M := M) act H hfinA
  -- the descended functional
  obtain ⟨Λ, hΛ⟩ := aux_descend_functional (p := p) (N := N) act H lam hadd hcob
  -- apply the finite duality
  have hU : ∀ y : (WM ⧸ SM), y ∈ (⊥ : Submodule (ZMod p) (WM ⧸ SM)) ↔
      ∀ x ∈ (⊤ : Submodule (ZMod p) (WN ⧸ SN)), β3 x y = 0 := by
    intro y
    rw [Submodule.mem_bot]
    constructor
    · intro hy x _
      rw [hy]
      simp
    · intro hy
      exact hnondegR y (fun x => hy x Submodule.mem_top)
  obtain ⟨hreal, -, -⟩ := pt_localPairingDual (p := p) β3 hnondegL hnondegR
    (⊤ : Submodule (ZMod p) (WN ⧸ SN)) (⊥ : Submodule (ZMod p) (WM ⧸ SM)) hU
  obtain ⟨x0, hx0⟩ := hreal Λ
  obtain ⟨a0, ha0⟩ := Submodule.Quotient.mk_surjective SM x0
  refine ⟨a0.1, (hca a0).1, (hca a0).2, fun b hb hb' => ?_⟩
  let bW : WN := ⟨b, (mem_cocycleLocConst (p := p) act H b).mpr ⟨hb, hb'⟩⟩
  have key := hx0 (Submodule.Quotient.mk bW)
  rw [hΛ bW, ← ha0, hβ3 a0 bW] at key
  exact key.symm

end Work.SSGRoute.PT
