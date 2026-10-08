/-
Copyright (c) 2024. All rights reserved.

# Module form of the type-`B` scalar dichotomy

`Work.Higman.scalar_module_of_layers`: a finite `𝔽₂`-vector space `V` carrying a linear
endomorphism `σ` of order `q - 1`, fixed-point-free on `V \ {0}`, with `|V| = q ^ 2` and with
at least `q + 1` `σ`-invariant subspaces of cardinality `q`, is (as an `𝔽₂[σ]`-module) the
square of a field of order `q` on which `σ` acts as a scalar.

The argument is the one sketched in the statement: `σ` acts freely on `V \ {0}`, so the orbits
of `⟨σ⟩` on `V \ {0}` all have size `q - 1`; the hypothesis `hN` supplies a `σ`-invariant
subspace `U` of cardinality `q`, whose non-zero vectors therefore form a single orbit, so `U` is
`σ`-simple.  Two distinct such subspaces `S ≠ T` are then simple with `S ⊓ T = ⊥` and, by
dimension, `S ⊔ T = ⊤`.  If `S ≅ T` as `𝔽₂[σ]`-modules, `V ≅ 𝔽_q²` with `σ` scalar (the Singer
cycle structure of `σ` on `S`, `Work.Higman.exists_singer_iso`, transported along the
isomorphism).  If `S ≇ T`, the only `σ`-simple subspaces of `V = S ⊕ T` are `S` and `T`, so
there are at most two invariant subspaces of cardinality `q`, contradicting `hN`.
-/

import Mathlib
import Submission.Work.Higman.scalar_defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.Higman

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-! ## Elementary facts about `Inv` and `SimpleMod` -/

lemma SimpleMod.inv {σ : V →ₗ[ZMod 2] V} {U : Submodule (ZMod 2) V} (h : SimpleMod σ U) :
    Inv σ U := h.1

lemma SimpleMod.ne_bot {σ : V →ₗ[ZMod 2] V} {U : Submodule (ZMod 2) V} (h : SimpleMod σ U) :
    U ≠ ⊥ := h.2.1

lemma SimpleMod.sub {σ : V →ₗ[ZMod 2] V} {U : Submodule (ZMod 2) V} (h : SimpleMod σ U)
    {W : Submodule (ZMod 2) V} (hWU : W ≤ U) (hW : Inv σ W) : W = ⊥ ∨ W = U := h.2.2 W hWU hW

/-- If `W ≤ U` with both `σ`-simple then `W = U`. -/
lemma SimpleMod.eq_of_le {σ : V →ₗ[ZMod 2] V} {U W : Submodule (ZMod 2) V}
    (hU : SimpleMod σ U) (hW : SimpleMod σ W) (h : W ≤ U) : W = U := by
  rcases hU.sub h hW.inv with h0 | h1
  · exact absurd h0 hW.ne_bot
  · exact h1

/-- Two distinct `σ`-simple subspaces meet in `⊥`. -/
lemma SimpleMod.inf_eq_bot {σ : V →ₗ[ZMod 2] V} {U W : Submodule (ZMod 2) V}
    (hU : SimpleMod σ U) (hW : SimpleMod σ W) (hne : U ≠ W) : U ⊓ W = ⊥ := by
  rcases hU.sub inf_le_left (hU.inv.inf hW.inv) with h0 | h1
  · exact h0
  · exact absurd (hW.eq_of_le hU (h1 ▸ inf_le_right)) hne

/-! ## The restriction of `σ` to an invariant subspace -/

lemma restr_pow_coe (σ : V →ₗ[ZMod 2] V) {U : Submodule (ZMod 2) V} (hU : Inv σ U)
    (k : ℕ) (x : U) : ((restr σ hU ^ k) x : V) = (σ ^ k) x := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, restr_apply, ih]

lemma restr_injective (σ : V →ₗ[ZMod 2] V) {U : Submodule (ZMod 2) V} (hU : Inv σ U)
    (hσ : Function.Injective σ) : Function.Injective (restr σ hU) := by
  intro a b hab
  exact Subtype.ext (hσ (by simpa using congrArg (fun z : U => (z : V)) hab))

/-- If `σ ^ (q - 1) = 1` with `q ≥ 2` then `σ` is injective. -/
lemma injective_of_pow_eq_one (σ : V →ₗ[ZMod 2] V) {q : ℕ} (hq : 2 ≤ q)
    (h : σ ^ (q - 1) = 1) : Function.Injective σ := by
  intro x y hxy
  have hz : ∀ z : V, (σ ^ (q - 1)) z = z := by
    intro z; rw [h]; rfl
  have hsplit : σ ^ (q - 1) = σ ^ (q - 2) * σ := by
    rw [← pow_succ, show q - 2 + 1 = q - 1 from by omega]
  calc x = (σ ^ (q - 1)) x := (hz x).symm
    _ = (σ ^ (q - 2) * σ) x := by rw [hsplit]
    _ = (σ ^ (q - 2)) (σ x) := rfl
    _ = (σ ^ (q - 2)) (σ y) := by rw [hxy]
    _ = (σ ^ (q - 2) * σ) y := rfl
    _ = (σ ^ (q - 1)) y := by rw [hsplit]
    _ = y := hz y

lemma Inv.pow_mem {σ : V →ₗ[ZMod 2] V} {W : Submodule (ZMod 2) V} (hW : Inv σ W)
    (k : ℕ) {w : V} (hw : w ∈ W) : (σ ^ k) w ∈ W := by
  induction k with
  | zero => simpa using hw
  | succ k ih => rw [pow_succ', Module.End.mul_apply]; exact hW _ ih

lemma pow_injective_of_injective (σ : V →ₗ[ZMod 2] V) (hσ : Function.Injective σ) :
    ∀ m : ℕ, Function.Injective (σ ^ m : V →ₗ[ZMod 2] V) := by
  intro m
  induction m with
  | zero => intro a b hab; simpa using hab
  | succ m ih =>
      intro a b hab
      rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply] at hab
      exact ih (hσ hab)

/-! ## `σ`-invariant subspaces of cardinality `q` are simple

Since `σ` acts freely on `V \ {0}` and `orderOf σ = q - 1`, every orbit of `⟨σ⟩` on the non-zero
vectors has cardinality exactly `q - 1`.  A `σ`-invariant subspace `U` with `|U| = q` has exactly
`q - 1` non-zero vectors, so they form a single orbit and `U` is `σ`-simple. -/

theorem simple_of_finrank {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (σ : V →ₗ[ZMod 2] V) {q n : ℕ} (hn : 1 ≤ n) (hqn : q = 2 ^ n)
    (hσ : orderOf σ = q - 1)
    (hfpf : ∀ k : ℕ, σ ^ k ≠ 1 → ∀ v : V, (σ ^ k) v = v → v = 0)
    {U : Submodule (ZMod 2) V} (hU : Inv σ U) (hdim : Module.finrank (ZMod 2) U = n) :
    SimpleMod σ U := by
  classical
  have hq2 : 2 ≤ q := by
    rw [hqn]
    exact le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn)
  have hσpow : σ ^ (q - 1) = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hσinj : Function.Injective σ := injective_of_pow_eq_one σ hq2 hσpow
  have hsinj : ∀ m : ℕ, Function.Injective (σ ^ m : V →ₗ[ZMod 2] V) :=
    pow_injective_of_injective σ hσinj
  have hrinj : Function.Injective (restr σ hU) := restr_injective σ hU hσinj
  have hrpowinj : ∀ m : ℕ, Function.Injective ((restr σ hU) ^ m : U →ₗ[ZMod 2] U) := by
    intro m
    induction m with
    | zero => intro a b hab; simpa using hab
    | succ m ih =>
        intro a b hab
        rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply] at hab
        exact ih (hrinj hab)
  have hcardU : Nat.card U = q := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := U), Nat.card_zmod, hdim, ← hqn]
  haveI : Fintype U := Fintype.ofFinite U
  have hcardU' : Fintype.card U = q := by rw [← Nat.card_eq_fintype_card]; exact hcardU
  -- transitivity of `⟨σ⟩` on the non-zero vectors of `U`
  have htrans : ∀ u v : U, u ≠ 0 → v ≠ 0 → ∃ k : ℕ, (restr σ hU ^ k) u = v := by
    intro u v hu hv
    have hcard_nz : Fintype.card {x : U // x ≠ 0} = q - 1 := by
      have h1 : Fintype.card {x : U // x = 0} = 1 := by
        rw [Fintype.card_eq_one_iff]
        exact ⟨⟨0, rfl⟩, fun y => Subtype.ext y.2⟩
      rw [Fintype.card_subtype_compl (fun x : U => x = 0), h1, hcardU']
    have hrnz : ∀ m : ℕ, (restr σ hU ^ m) u ≠ 0 := by
      intro m h0
      exact hu (hrpowinj m (by rw [h0, map_zero]))
    let g : Fin (q - 1) → {x : U // x ≠ 0} := fun k => ⟨(restr σ hU ^ (k : ℕ)) u, hrnz _⟩
    have hginj : Function.Injective g := by
      intro k k' hkk
      have h1 : (restr σ hU ^ (k : ℕ)) u = (restr σ hU ^ (k' : ℕ)) u :=
        congrArg Subtype.val hkk
      have h2 : (σ ^ (k : ℕ)) u.1 = (σ ^ (k' : ℕ)) u.1 := by
        have := congrArg (fun z : U => (z : V)) h1
        simpa [restr_pow_coe] using this
      have go : ∀ (a b : Fin (q - 1)), (σ ^ (a : ℕ)) u.1 = (σ ^ (b : ℕ)) u.1 →
          (a : ℕ) ≤ (b : ℕ) → a = b := by
        intro a b hab hle
        rcases Nat.eq_or_lt_of_le hle with heq | hlt
        · exact Fin.ext heq
        · exfalso
          have hpos : 0 < (b : ℕ) - (a : ℕ) := by omega
          have hlt' : (b : ℕ) - (a : ℕ) < q - 1 := by have := b.isLt; omega
          have h3 : (σ ^ ((b : ℕ) - (a : ℕ))) u.1 = u.1 := by
            have key : (σ ^ (a : ℕ)) ((σ ^ ((b : ℕ) - (a : ℕ))) u.1) = (σ ^ (a : ℕ)) u.1 := by
              rw [← Module.End.mul_apply, ← pow_add, Nat.add_sub_of_le hle]
              exact hab.symm
            exact hsinj (a : ℕ) key
          have hne1 : σ ^ ((b : ℕ) - (a : ℕ)) ≠ 1 := by
            intro hcon
            have hdvd : orderOf σ ∣ ((b : ℕ) - (a : ℕ)) :=
              orderOf_dvd_iff_pow_eq_one.mpr hcon
            rw [hσ] at hdvd
            have := Nat.le_of_dvd hpos hdvd
            omega
          exact hu (Subtype.ext (hfpf _ hne1 u.1 h3))
      rcases le_total (k : ℕ) (k' : ℕ) with hle | hle
      · exact go k k' h2 hle
      · exact (go k' k h2.symm hle).symm
    have hbij : Function.Bijective g := by
      rw [Fintype.bijective_iff_injective_and_card]
      exact ⟨hginj, by rw [Fintype.card_fin, hcard_nz]⟩
    obtain ⟨k, hk⟩ := hbij.2 ⟨v, hv⟩
    exact ⟨(k : ℕ), congrArg Subtype.val hk⟩
  refine ⟨hU, ?_, ?_⟩
  · intro hbot
    have h0 : Module.finrank (ZMod 2) U = 0 := Submodule.finrank_eq_zero.mpr hbot
    omega
  · intro W hWU hW
    by_cases hWbot : W = ⊥
    · exact Or.inl hWbot
    · refine Or.inr (le_antisymm hWU ?_)
      obtain ⟨w, hwW, hw0⟩ := (Submodule.ne_bot_iff W).mp hWbot
      intro v hv
      rcases eq_or_ne v 0 with rfl | hv0
      · exact W.zero_mem
      · obtain ⟨k, hk⟩ := htrans ⟨w, hWU hwW⟩ ⟨v, hv⟩
          (fun h => hw0 (congrArg Subtype.val h)) (fun h => hv0 (congrArg Subtype.val h))
        have hveq : (σ ^ k) w = v := by
          have := congrArg (fun z : U => (z : V)) hk
          simpa [restr_pow_coe] using this
        rw [← hveq]
        exact hW.pow_mem k hwW

/-! ## The two counts agree -/

/-- The `σ`-invariant `𝔽₂`-submodules of `V` of dimension `n` correspond bijectively to the
`σ`-invariant additive subgroups of `V` of cardinality `q`, when `q = 2 ^ n`. -/
theorem card_invSubmodule_eq_card_addSubgroup {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] (σ : V →ₗ[ZMod 2] V) {q n : ℕ} (hqn : q = 2 ^ n) :
    Nat.card {U : Submodule (ZMod 2) V // Inv σ U ∧ Module.finrank (ZMod 2) U = n} =
      Nat.card {N : AddSubgroup V // (∀ v ∈ N, σ v ∈ N) ∧ Nat.card N = q} := by
  let e : AddSubgroup V ≃ Submodule (ZMod 2) V :=
    { toFun := fun N => AddSubgroup.toZModSubmodule 2 N
      invFun := fun U => (AddSubgroup.toZModSubmodule 2).symm U
      left_inv := fun N => (AddSubgroup.toZModSubmodule 2).symm_apply_apply N
      right_inv := fun U => (AddSubgroup.toZModSubmodule 2).apply_symm_apply U }
  refine (Nat.card_congr (Equiv.subtypeEquiv e ?_)).symm
  intro N
  have heN : e N = AddSubgroup.toZModSubmodule 2 N := rfl
  rw [heN]
  have hcardN : Nat.card ↥N = Nat.card ↥(AddSubgroup.toZModSubmodule 2 N) :=
    Nat.card_congr (Equiv.subtypeEquivRight
      fun x => (AddSubgroup.mem_toZModSubmodule 2).symm)
  constructor
  · rintro ⟨hinv, hcard⟩
    refine ⟨fun v hv => hinv v hv, ?_⟩
    have h1 : Nat.card ↥(AddSubgroup.toZModSubmodule 2 N) = 2 ^ n := by
      rw [← hcardN, hcard, hqn]
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := ↥(AddSubgroup.toZModSubmodule 2 N)), Nat.card_zmod] at h1
    exact Nat.pow_right_injective (le_refl 2) h1
  · rintro ⟨hinv, hdim⟩
    refine ⟨fun v hv => hinv v hv, ?_⟩
    have h1 : Module.finrank (ZMod 2) ↥(AddSubgroup.toZModSubmodule 2 N) = n := hdim
    rw [hcardN, Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := ↥(AddSubgroup.toZModSubmodule 2 N)), Nat.card_zmod, h1, hqn]

/-! ## Composition of `𝔽₂[σ]`-equivalences -/

lemma EqvIso.symm {σ : V →ₗ[ZMod 2] V} {S T : Submodule (ZMod 2) V} (h : EqvIso σ S T) :
    EqvIso σ T S := by
  obtain ⟨hS, hT, e, he⟩ := h
  refine ⟨hT, hS, e.symm, fun x => ?_⟩
  apply e.injective
  rw [e.apply_symm_apply, he, e.apply_symm_apply]

lemma EqvIso.trans {σ : V →ₗ[ZMod 2] V} {R S T : Submodule (ZMod 2) V}
    (h₁ : EqvIso σ R S) (h₂ : EqvIso σ S T) : EqvIso σ R T := by
  obtain ⟨hR, hS, e₁, he₁⟩ := h₁
  obtain ⟨hS', hT, e₂, he₂⟩ := h₂
  refine ⟨hR, hT, e₁.trans e₂, fun x => ?_⟩
  simp only [LinearEquiv.trans_apply]
  rw [he₁ x, he₂ (e₁ x)]

lemma EqvIso.ofLinearMap {σ : V →ₗ[ZMod 2] V} {S T : Submodule (ZMod 2) V}
    (hS : Inv σ S) (hT : Inv σ T) (f : S →ₗ[ZMod 2] T) (hbij : Function.Bijective f)
    (hf : ∀ x : S, f (restr σ hS x) = restr σ hT (f x)) : EqvIso σ S T :=
  ⟨hS, hT, LinearEquiv.ofBijective f hbij, fun x => hf x⟩

/-- `S ⊓ T = ⊥` and `S ⊔ T = ⊤` say that `S` and `T` are complements. -/
lemma isCompl_of_inf_eq_bot_sup_eq_top {S T : Submodule (ZMod 2) V}
    (hdisj : S ⊓ T = ⊥) (hsup : S ⊔ T = ⊤) : IsCompl S T :=
  ⟨disjoint_iff_inf_le.mpr (le_of_eq hdisj), codisjoint_iff_le_sup.mpr (le_of_eq hsup.symm)⟩

/-! ## The projection along a complement is `σ`-equivariant -/

lemma projectionOnto_equivariant {σ : V →ₗ[ZMod 2] V} {S T : Submodule (ZMod 2) V}
    (hS : Inv σ S) (hT : Inv σ T) (hcompl : IsCompl S T) (v : V) :
    restr σ hS (S.projectionOnto T hcompl v) = S.projectionOnto T hcompl (σ v) := by
  have hmem : v - (S.projectionOnto T hcompl v : V) ∈ T := by
    have h0 : S.projectionOnto T hcompl (v - (S.projectionOnto T hcompl v : V)) = 0 := by
      rw [map_sub, Submodule.projectionOnto_apply_of_mem_left hcompl (SetLike.coe_mem _),
        sub_self]
    exact (Submodule.projectionOnto_apply_eq_zero_iff hcompl).mp h0
  have hv : σ v = σ (S.projectionOnto T hcompl v : V)
      + σ (v - (S.projectionOnto T hcompl v : V)) := by
    conv_lhs => rw [show v = (S.projectionOnto T hcompl v : V)
      + (v - (S.projectionOnto T hcompl v : V)) from by abel]
    rw [map_add]
  rw [hv, map_add,
    Submodule.projectionOnto_apply_of_mem_left hcompl (hS _ (SetLike.coe_mem _)),
    Submodule.projectionOnto_apply_of_mem_right hcompl (hT _ hmem), add_zero]
  exact Subtype.ext rfl

/-! ## A simple subspace `U` with `U ⊓ T = ⊥` inside `V = S ⊕ T` is `𝔽₂[σ]`-isomorphic to `S` -/

lemma eqvIso_of_isCompl {σ : V →ₗ[ZMod 2] V} {S T U : Submodule (ZMod 2) V}
    (hS : SimpleMod σ S) (hT : SimpleMod σ T) (hU : SimpleMod σ U)
    (hcompl : IsCompl S T) (hinf : U ⊓ T = ⊥) : EqvIso σ U S := by
  classical
  let g : U →ₗ[ZMod 2] S := (S.projectionOnto T hcompl).comp U.subtype
  have hgker : ∀ u : U, g u = 0 ↔ u = 0 := by
    intro u
    constructor
    · intro h
      have h1 : (u : V) ∈ T := (Submodule.projectionOnto_apply_eq_zero_iff hcompl).mp h
      have h2 : (u : V) ∈ U ⊓ T := ⟨u.2, h1⟩
      rw [hinf, Submodule.mem_bot] at h2
      exact Subtype.ext h2
    · rintro rfl; exact map_zero g
  have hginj : Function.Injective g := fun a b hab => by
    have h1 : g (a - b) = 0 := by rw [map_sub, hab, sub_self]
    have h2 : a - b = 0 := (hgker _).mp h1
    rwa [sub_eq_zero] at h2
  have hgeq : ∀ x : U, g (restr σ hU.inv x) = restr σ hS.inv (g x) := fun x =>
    (projectionOnto_equivariant hS.inv hT.inv hcompl (x : V)).symm
  have hMle : (g.range).map S.subtype ≤ S := Submodule.map_subtype_le (p := S) g.range
  have hMinv : Inv σ ((g.range).map S.subtype) := by
    intro w hw
    rw [Submodule.mem_map] at hw ⊢
    obtain ⟨s, hs, hsw⟩ := hw
    rw [LinearMap.mem_range] at hs
    obtain ⟨u, hu⟩ := hs
    refine ⟨restr σ hS.inv s, ⟨restr σ hU.inv u, ?_⟩, ?_⟩
    · rw [← hu]; exact hgeq u
    · have hsw' : (s : V) = w := hsw
      show ((restr σ hS.inv s : S) : V) = σ w
      rw [restr_apply, hsw']
  have hMne : (g.range).map S.subtype ≠ ⊥ := by
    intro hbot
    have hrbot : g.range = ⊥ := by
      have hmap : Submodule.map S.subtype (LinearMap.range g)
          = Submodule.map S.subtype (⊥ : Submodule (ZMod 2) S) := by
        rw [Submodule.map_bot]
        exact hbot
      exact Submodule.map_injective_of_injective (Submodule.subtype_injective S) hmap
    obtain ⟨u, hu⟩ := (Submodule.ne_bot_iff U).mp hU.ne_bot
    have hmem : g ⟨u, hu.1⟩ ∈ g.range := ⟨_, rfl⟩
    rw [hrbot, Submodule.mem_bot] at hmem
    have hzero : (⟨u, hu.1⟩ : U) ∈ LinearMap.ker g := by
      rw [LinearMap.mem_ker]; exact hmem
    rw [LinearMap.ker_eq_bot.mpr hginj, Submodule.mem_bot] at hzero
    exact hu.2 (congrArg Subtype.val hzero)
  have hMS : (g.range).map S.subtype = S := by
    rcases hS.2.2 ((g.range).map S.subtype) hMle hMinv with h | h
    · exact absurd h hMne
    · exact h
  have hgsurj : Function.Surjective g := by
    intro y
    have hy : (y : V) ∈ (g.range).map S.subtype := by rw [hMS]; exact y.2
    rw [Submodule.mem_map] at hy
    obtain ⟨s, hs, hsy⟩ := hy
    rw [LinearMap.mem_range] at hs
    obtain ⟨u, hu⟩ := hs
    exact ⟨u, by rw [hu]; exact Subtype.ext hsy⟩
  exact EqvIso.ofLinearMap hU.inv hS.inv g ⟨hginj, hgsurj⟩ hgeq

/-- If `V = S ⊕ T` with `S`, `T` `σ`-simple and not isomorphic as `𝔽₂[σ]`-modules, then every
`σ`-simple subspace of `V` is `S` or `T`. -/
theorem simple_eq_left_or_right {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (σ : V →ₗ[ZMod 2] V) {S T U : Submodule (ZMod 2) V}
    (hS : SimpleMod σ S) (hT : SimpleMod σ T) (hU : SimpleMod σ U)
    (hdisj : S ⊓ T = ⊥) (hsup : S ⊔ T = ⊤) (hnoiso : ¬ EqvIso σ S T) :
    U = S ∨ U = T := by
  classical
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hUS, hUT⟩ := hcon
  have hcompl : IsCompl S T := isCompl_of_inf_eq_bot_sup_eq_top hdisj hsup
  have hinfS : U ⊓ S = ⊥ := SimpleMod.inf_eq_bot hU hS hUS
  have hinfT : U ⊓ T = ⊥ := SimpleMod.inf_eq_bot hU hT hUT
  have h1 : EqvIso σ U T := eqvIso_of_isCompl hT hS hU hcompl.symm hinfS
  have h2 : EqvIso σ U S := eqvIso_of_isCompl hS hT hU hcompl hinfT
  exact hnoiso (h2.symm.trans h1)

/-- If `w = a + b` with `a ∈ S`, `b ∈ T` and `S`, `T` complementary, then `(a, b)` are the
coordinates of `w`. -/
lemma prodEquiv_symm_apply_eq {S T : Submodule (ZMod 2) V} (h : IsCompl S T)
    {w : V} {a : ↥S} {b : ↥T} (hw : (a : V) + (b : V) = w) :
    (S.prodEquivOfIsCompl T h).symm w = (a, b) := by
  refine (S.prodEquivOfIsCompl T h).symm_apply_eq.mpr ?_
  rw [Submodule.coe_prodEquivOfIsCompl']
  exact hw.symm

/-- **Construction of the scalar module from two isomorphic constituents.**  Let `V` be a finite
`𝔽₂`-vector space with `S`, `T` complementary `σ`-invariant subspaces, `S` of cardinality
`2 ^ n` (`n ≥ 1`, `q = 2 ^ n`), `σ ≠ 1`, and suppose `S` and `T` are isomorphic as `𝔽₂[σ]`-modules
(`EqvIso σ S T`).  Then `V` is isomorphic as an `𝔽₂[σ]`-module to the square of the field
`𝔽_q`, with `σ` acting as a scalar. -/
theorem exists_scalar_module_of_iso {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (σ : V →ₗ[ZMod 2] V) {q n : ℕ} (hn : 1 ≤ n) (hqn : q = 2 ^ n) (hσne : σ ≠ 1)
    (hσ : orderOf σ = q - 1)
    (hfpf : ∀ k : ℕ, σ ^ k ≠ 1 → ∀ v : V, (σ ^ k) v = v → v = 0)
    {S T : Submodule (ZMod 2) V} (hcompl : IsCompl S T) (hcardS : Nat.card ↥S = 2 ^ n)
    (he : EqvIso σ S T) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F) (ψ : V ≃ (F × F)) (lam : Fˣ),
      Nat.card F = q ∧ (∀ x y, ψ (x + y) = ψ x + ψ y) ∧ ∀ v, ψ (σ v) = (lam : F) • ψ v := by
  classical
  obtain ⟨hSinv, hTinv, e, hee⟩ := he
  have hq2 : 2 ≤ q := by
    rw [hqn]
    exact le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn)
  have hσpow : σ ^ (q - 1) = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hσinj : Function.Injective σ := injective_of_pow_eq_one σ hq2 hσpow
  haveI : Fintype ↥S := Fintype.ofFinite _
  have hSnt : Nontrivial ↥S := Fintype.one_lt_card_iff_nontrivial.mp (by
    rw [← Nat.card_eq_fintype_card, hcardS]
    exact Nat.one_lt_pow (by omega) (by norm_num))
  -- the Singer cycle `ξ` induced by `σ` on `S`
  have hSinj : Function.Injective (restr σ hSinv) := restr_injective σ hSinv hσinj
  let ξ : ↥S ≃ₗ[ZMod 2] ↥S := LinearEquiv.ofBijective (restr σ hSinv)
    ⟨hSinj, (Finite.injective_iff_surjective).mp hSinj⟩
  have hξcoe : (↑ξ : ↥S →ₗ[ZMod 2] ↥S) = restr σ hSinv := LinearMap.ext fun x => rfl
  have hξpow : ∀ k : ℕ, (↑(ξ ^ k) : ↥S →ₗ[ZMod 2] ↥S) = (restr σ hSinv) ^ k := by
    intro k
    induction k with
    | zero =>
        rw [pow_zero, pow_zero, LinearEquiv.coe_toLinearMap_one]
        rfl
    | succ k ih =>
        rw [pow_succ, pow_succ, LinearEquiv.coe_toLinearMap_mul, ih, hξcoe]
  have hξord : orderOf ξ = 2 ^ n - 1 := by
    have hfaithful : ∀ m : ℕ, ξ ^ m = 1 → σ ^ m = 1 := by
      intro m hm
      have hmap : (restr σ hSinv) ^ m = 1 := by
        rw [← hξpow m, hm]
        rfl
      by_contra hne
      obtain ⟨x, hx⟩ := exists_ne (0 : ↥S)
      have hx1 : (σ ^ m) x.1 = x.1 := by
        have h := congrArg (fun f : ↥S →ₗ[ZMod 2] ↥S => f x) hmap
        rw [Module.End.one_apply] at h
        have h2 : (((restr σ hSinv) ^ m) x : V) = (x : V) := congrArg Subtype.val h
        rwa [restr_pow_coe] at h2
      exact hx (Subtype.ext (hfpf m hne x.1 hx1))
    have hpow : ξ ^ (q - 1) = 1 := by
      apply LinearEquiv.ext
      intro x
      have h3 : (ξ ^ (q - 1)) x = ((restr σ hSinv) ^ (q - 1)) x :=
        congrArg (fun f : ↥S →ₗ[ZMod 2] ↥S => f x) (hξpow (q - 1))
      rw [h3]
      exact Subtype.ext (by rw [restr_pow_coe, hσpow]; rfl)
    have h1 : orderOf ξ ∣ q - 1 := orderOf_dvd_iff_pow_eq_one.mpr hpow
    rw [hqn] at h1
    have h2 : (q - 1) ∣ orderOf ξ := by
      have hm := hfaithful (orderOf ξ) (pow_orderOf_eq_one ξ)
      have h3 : orderOf σ ∣ orderOf ξ := orderOf_dvd_iff_pow_eq_one.mpr hm
      rwa [hσ] at h3
    rw [hqn] at h2
    exact Nat.dvd_antisymm h1 h2
  have hξfree : ∀ v : ↥S, ξ v = v → v = 0 := by
    intro v hv
    have h : ((restr σ hSinv) v : V) = (v : V) := congrArg (fun z : ↥S => (z : V)) hv
    have h2 : (σ ^ 1) (v : V) = (v : V) := by
      have h3 : (((restr σ hSinv) ^ 1) v : V) = (v : V) := by simpa using h
      simpa [restr_pow_coe] using h3
    exact Subtype.ext (hfpf 1 hσne (v : V) h2)
  obtain ⟨φ, lam, hlamord, hφeq⟩ :=
    exists_singer_iso (V := ↥S) (n := n) (by omega : 0 < n) hcardS ξ hξord hξfree
  -- transport the field coordinates to `T` along `e`
  let φT : ↥T ≃ₗ[ZMod 2] GaloisField 2 n := e.symm.trans φ
  have hφTeq : ∀ y : ↥T, φT (restr σ hTinv y) = (lam : GaloisField 2 n) * φT y := by
    intro y
    have hesymm : e.symm (restr σ hTinv y) = restr σ hSinv (e.symm y) := by
      have hh := congrArg (fun z : ↥T => e.symm z) (hee (e.symm y))
      rw [e.symm_apply_apply, e.apply_symm_apply] at hh
      exact hh.symm
    show φ (e.symm (restr σ hTinv y)) = (lam : GaloisField 2 n) * φ (e.symm y)
    rw [hesymm]
    exact hφeq (e.symm y)
  let Ψ : V ≃ₗ[ZMod 2] (GaloisField 2 n × GaloisField 2 n) :=
    (S.prodEquivOfIsCompl T hcompl).symm.trans (LinearEquiv.prodCongr φ φT)
  have key : ∀ (a : ↥S) (b : ↥T),
      Ψ (σ ((S.prodEquivOfIsCompl T hcompl) (a, b)))
        = (lam : GaloisField 2 n) • Ψ ((S.prodEquivOfIsCompl T hcompl) (a, b)) := by
    intro a b
    have hσ' : σ ((S.prodEquivOfIsCompl T hcompl) (a, b))
        = (S.prodEquivOfIsCompl T hcompl) (restr σ hSinv a, restr σ hTinv b) := by
      rw [Submodule.coe_prodEquivOfIsCompl', Submodule.coe_prodEquivOfIsCompl', map_add,
        restr_apply, restr_apply]
    change (LinearEquiv.prodCongr φ φT)
        ((S.prodEquivOfIsCompl T hcompl).symm (σ ((S.prodEquivOfIsCompl T hcompl) (a, b))))
      = (lam : GaloisField 2 n) • (LinearEquiv.prodCongr φ φT)
        ((S.prodEquivOfIsCompl T hcompl).symm ((S.prodEquivOfIsCompl T hcompl) (a, b)))
    rw [hσ']
    simp only [LinearEquiv.symm_apply_apply, LinearEquiv.prodCongr_apply]
    have h1 : φ (restr σ hSinv a) = (lam : GaloisField 2 n) * φ a := hφeq a
    have h2 : φT (restr σ hTinv b) = (lam : GaloisField 2 n) * φT b := hφTeq b
    rw [h1, h2]
    rfl
  have hΨ : ∀ v : V, Ψ (σ v) = (lam : GaloisField 2 n) • Ψ v := by
    intro v
    conv_lhs => rw [← LinearEquiv.apply_symm_apply (S.prodEquivOfIsCompl T hcompl) v]
    conv_rhs => rw [← LinearEquiv.apply_symm_apply (S.prodEquivOfIsCompl T hcompl) v]
    exact key _ _
  exact ⟨GaloisField 2 n, inferInstance, Fintype.ofFinite _, Ψ.toEquiv, lam,
    by rw [GaloisField.card 2 n (by omega : n ≠ 0), ← hqn],
    fun x y => Ψ.map_add x y, hΨ⟩

/-- **Module form of the type-`B` scalar dichotomy.**

Let `V` be a finite `𝔽₂`-vector space and `σ` a linear endomorphism of `V` with `orderOf σ = q - 1`,
`|V| = q ^ 2`, `2 ≤ q`, acting fixed-point-freely on `V \ {0}` (every power `σ ^ k ≠ 1` has no
nonzero fixed vector).  Suppose there are at least `q + 1` `σ`-invariant additive subgroups of
cardinality `q` (i.e. `σ`-invariant subspaces of dimension `log₂ q`).

Then there is a field `F` of order `q` and an additive bijection `V ≃ F × F` which intertwines `σ`
with multiplication by a scalar `λ ∈ Fˣ`.

Mathematical content: the minimal polynomial `m` of `σ` divides `X ^ (q - 1) - 1`, which is
squarefree (char 2, `q - 1` odd), so `V` is the direct sum of the `ker (mᵢ (σ))` over the distinct
irreducible factors `mᵢ` of `m`; fixed-point-freeness forces every root `λᵢ` of `mᵢ` to have order
exactly `q - 1`, so `deg mᵢ = n` where `q = 2 ^ n`; hence `V` has at most two constituents.  With
two non-isomorphic constituents the only `σ`-invariant subspaces are `0, V₁, V₂, V` (only two of
dimension `n`), contradicting the hypothesis; so there is a single irreducible `m` of degree `n`
with `V ≅ (𝔽₂[X]/(m))²`, i.e. `V ≅ F²` for the field `F = 𝔽₂[X]/(m)` of order `q`, with `σ` acting
as the scalar `λ = X mod m`. -/
theorem scalar_module_of_layers {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (σ : V →ₗ[ZMod 2] V) (q : ℕ) (hq : 2 ≤ q) (hcardV : Nat.card V = q ^ 2)
    (hσ : orderOf σ = q - 1)
    (hfpf : ∀ k : ℕ, σ ^ k ≠ 1 → ∀ v : V, (σ ^ k) v = v → v = 0)
    (hN : q + 1 ≤ Nat.card {N : AddSubgroup V // (∀ v ∈ N, σ v ∈ N) ∧ Nat.card N = q}) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F) (ψ : V ≃ (F × F)) (lam : Fˣ),
      Nat.card F = q ∧ (∀ x y, ψ (x + y) = ψ x + ψ y) ∧ ∀ v, ψ (σ v) = (lam : F) • ψ v := by
  classical
  -- Step 1: an invariant subgroup of cardinality `q` gives `n` with `q = 2 ^ n`
  have hposN : 0 < Nat.card {N : AddSubgroup V // (∀ v ∈ N, σ v ∈ N) ∧ Nat.card N = q} := by
    omega
  obtain ⟨hneN, _⟩ := Nat.card_pos_iff.mp hposN
  obtain ⟨N₀⟩ := hneN
  let U₀ : Submodule (ZMod 2) V := AddSubgroup.toZModSubmodule 2 N₀.1
  have hU₀inv : Inv σ U₀ := fun v hv => N₀.2.1 v hv
  have hbridge : Nat.card ↥N₀.1 = Nat.card ↥U₀ :=
    Nat.card_congr (Equiv.subtypeEquivRight
      fun x => (AddSubgroup.mem_toZModSubmodule 2).symm)
  set n : ℕ := Module.finrank (ZMod 2) U₀ with hn_def
  have hqn : q = 2 ^ n := by
    rw [← N₀.2.2, hbridge, Module.natCard_eq_pow_finrank (K := ZMod 2) (V := U₀),
      Nat.card_zmod, hn_def]
  have hn_pos : 1 ≤ n := by
    have h2 : (2 : ℕ) ^ 1 ≤ 2 ^ n := by rw [← hqn]; exact hq
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h2
  have hVcard : Nat.card V = 2 ^ (2 * n) := by
    rw [hcardV, hqn]
    show (2 ^ n) ^ 2 = 2 ^ (2 * n)
    rw [← pow_mul, Nat.mul_comm]
  have hVdim : Module.finrank (ZMod 2) V = 2 * n := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)
    rw [hVcard, Nat.card_zmod] at h
    exact Nat.pow_right_injective (le_refl 2) h.symm
  -- Step 2: transfer the count of `hN` to the submodule count
  have hAcard : q + 1 ≤ Nat.card {U : Submodule (ZMod 2) V //
      Inv σ U ∧ Module.finrank (ZMod 2) U = n} := by
    rw [card_invSubmodule_eq_card_addSubgroup σ hqn]
    exact hN
  have hApos : 0 < Nat.card {U : Submodule (ZMod 2) V //
      Inv σ U ∧ Module.finrank (ZMod 2) U = n} := by omega
  obtain ⟨hneA, hfinA⟩ := Nat.card_pos_iff.mp hApos
  haveI : Fintype {U : Submodule (ZMod 2) V // Inv σ U ∧ Module.finrank (ZMod 2) U = n} :=
    Fintype.ofFinite _
  -- Step 3: two distinct such subspaces `S₁ ≠ S₂`
  obtain ⟨S₁⟩ := hneA
  have hA2 : 1 < Fintype.card {U : Submodule (ZMod 2) V //
      Inv σ U ∧ Module.finrank (ZMod 2) U = n} := by
    rw [← Nat.card_eq_fintype_card]; omega
  obtain ⟨S₂, hS₂ne⟩ := Fintype.exists_ne_of_one_lt_card hA2 S₁
  have hs1 : SimpleMod σ S₁.1 := simple_of_finrank σ hn_pos hqn hσ hfpf S₁.2.1 S₁.2.2
  have hs2 : SimpleMod σ S₂.1 := simple_of_finrank σ hn_pos hqn hσ hfpf S₂.2.1 S₂.2.2
  have hne12 : S₁.1 ≠ S₂.1 := fun h => hS₂ne (Subtype.ext h).symm
  have hdisj : S₁.1 ⊓ S₂.1 = ⊥ := SimpleMod.inf_eq_bot hs1 hs2 hne12
  have hsup : S₁.1 ⊔ S₂.1 = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [hVdim]
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq S₁.1 S₂.1
    rw [hdisj, S₁.2.2, S₂.2.2] at h1
    have h0 : Module.finrank (ZMod 2) (⊥ : Submodule (ZMod 2) V) = 0 :=
      Submodule.finrank_eq_zero.mpr rfl
    rw [h0, add_zero] at h1
    omega
  -- Step 4: if `S₁ ≅ S₂` build the scalar module; otherwise count
  by_cases hiso : EqvIso σ S₁.1 S₂.1
  · by_cases hσ1 : σ = 1
    · -- `σ = 1` forces `q = 2`: any additive equivalence works, with `λ = 1`
      have hq2 : q = 2 := by
        have h := hσ
        rw [hσ1, orderOf_one] at h
        omega
      have hn1 : n = 1 := by
        have h : (2 : ℕ) ^ n = 2 := by rw [← hqn, hq2]
        exact Nat.pow_right_injective (le_refl 2) h
      have hFdim : Module.finrank (ZMod 2) (GaloisField 2 n) = n := by
        have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := GaloisField 2 n)
        rw [Nat.card_zmod, GaloisField.card 2 n (by omega : n ≠ 0)] at h1
        exact (Nat.pow_right_injective (le_refl 2) h1).symm
      have hdim_eq : Module.finrank (ZMod 2) V
          = Module.finrank (ZMod 2) (GaloisField 2 n × GaloisField 2 n) := by
        rw [Module.finrank_prod, hFdim, hVdim, hn1]
      obtain ⟨e⟩ := FiniteDimensional.nonempty_linearEquiv_of_finrank_eq hdim_eq
      refine ⟨GaloisField 2 n, inferInstance, Fintype.ofFinite _, e.toEquiv, 1, ?_, ?_, ?_⟩
      · rw [GaloisField.card 2 n (by omega : n ≠ 0), ← hqn]
      · intro x y; exact e.map_add x y
      · intro v; rw [hσ1]; simp
    · refine exists_scalar_module_of_iso σ hn_pos hqn hσ1 hσ hfpf
        (isCompl_of_inf_eq_bot_sup_eq_top hdisj hsup) ?_ hiso
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥S₁.1), Nat.card_zmod, S₁.2.2]
  · exfalso
    have hcount : Nat.card {U : Submodule (ZMod 2) V //
        Inv σ U ∧ Module.finrank (ZMod 2) U = n} ≤ 2 := by
      have hkey : ∀ X : {U : Submodule (ZMod 2) V // Inv σ U ∧ Module.finrank (ZMod 2) U = n},
          (if X.1 = S₁.1 then (0 : Fin 2) else 1) = 0 → X.1 = S₁.1 := by
        intro X hx
        by_contra hc
        rw [if_neg hc] at hx
        exact absurd hx (by decide)
      have hle := Nat.card_le_card_of_injective
        (fun W : {U : Submodule (ZMod 2) V // Inv σ U ∧ Module.finrank (ZMod 2) U = n} =>
          if W.1 = S₁.1 then (0 : Fin 2) else 1) ?_
      · simpa using hle
      · intro W W' h
        change (if W.1 = S₁.1 then (0 : Fin 2) else 1)
          = (if W'.1 = S₁.1 then (0 : Fin 2) else 1) at h
        have kW : W.1 = S₁.1 ∨ W.1 = S₂.1 :=
          simple_eq_left_or_right σ hs1 hs2
            (simple_of_finrank σ hn_pos hqn hσ hfpf W.2.1 W.2.2) hdisj hsup hiso
        have kW' : W'.1 = S₁.1 ∨ W'.1 = S₂.1 :=
          simple_eq_left_or_right σ hs1 hs2
            (simple_of_finrank σ hn_pos hqn hσ hfpf W'.2.1 W'.2.2) hdisj hsup hiso
        by_cases hW : W.1 = S₁.1
        · have h0 : (if W.1 = S₁.1 then (0 : Fin 2) else 1) = 0 := by simp [hW]
          have : (if W'.1 = S₁.1 then (0 : Fin 2) else 1) = 0 := by
            rw [h0] at h; exact h.symm
          exact Subtype.ext (by rw [hW, hkey W' this])
        · have h1 : (if W.1 = S₁.1 then (0 : Fin 2) else 1) = 1 := by simp [hW]
          have h2 : (if W'.1 = S₁.1 then (0 : Fin 2) else 1) = 1 := by
            rw [h1] at h; exact h.symm
          have h3 : W'.1 ≠ S₁.1 := fun hc => by
            rw [if_pos hc] at h2
            exact absurd h2 (by decide)
          have hW2 : W.1 = S₂.1 := by rcases kW with hh | hh; exacts [absurd hh hW, hh]
          have hW2' : W'.1 = S₂.1 := by rcases kW' with hh | hh; exacts [absurd hh h3, hh]
          exact Subtype.ext (by rw [hW2, hW2'])
    omega

end Work.Higman
