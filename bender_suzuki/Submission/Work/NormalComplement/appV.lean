import Mathlib
import Submission.Work.NormalComplement.Sections
import Submission.Work.NormalComplement.AppVDefs
import Submission.Work.NormalComplement.AppVCore

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement

/-- **Peterfalvi I Appendix V (d)** (p.211), as the `Prop` `Work.NormalComplement.AppVProp`:
`Q` elementary abelian of exponent `d` (prime), `U ≤ N_G(Q)` acting faithfully on `Q`
(`U ⊓ C_G(Q) = ⊥`), `T ⊴ U` cyclic and irreducible on `Q`, `1 ≠ P ≤ U` with `|C_Q(P₁)| = d` for all
`1 ≠ P₁ ≤ P`; then `|P| = p` is prime, `|Q| = d^p`, and `C_U(s) = P` for `1 ≠ s ∈ C_Q(P)`.
(Note `P₁ = ⊥` is *excluded*: `|C_Q(⊥)| = |Q| = d` would force `P = 1`.  The core statement
`AppVCoreProp` demands `P₁ ≠ ⊥` for the same reason.)
Route: Schur's argument makes `F_d[T]` a finite field `F` with `Q` one-dimensional over `F`, so `U`
acts by semilinear maps (`U ⊓ C_G(Q) = 1` injects `U/C_U(Q) ↪ Aut(F)`, cyclic of order
`n = log_d |Q|`); each `1 ≠ P₁ ≤ P` injects into `Aut(F)` with fixed field `C_Q(P₁) = F_d`, so
`|P₁| = n`; hence `n` is prime, `|Q| = d^n`, and `C_U(s) = P` for `s ∈ C_Q(P)#`.

This file proves it by reduction to the linear-algebra core `appVCoreProp`
(`Submission/Work/NormalComplement/AppVCore.lean`): `V := Q` is made a `ZMod d`-module, `T = ⟨t₀⟩`
gives an irreducible linear automorphism `t` of `V`, `U` acts on `V` through the conjugation action
(injective by faithfulness), `P` maps to `P' ≤ U' = ρ(U)`, and the fixed-point hypothesis
`|C_V(P₁)| = d` is transferred along the correspondence between subspaces of `V` and subgroups of
`Q`.  The core then gives `|P'|` prime, `|V| = d ^ |P'|` and `C_{U'}(v) = P'` for `v ∈ C_V(P')#`,
which translate back to the statement. -/
theorem appV : Work.NormalComplement.AppVProp := by
  intro G _ _ d U Q T P hd hab hexp hQne hUN hTU hUT hTcyc hirr hfaith hPU hPne hfix
  classical
  haveI : Fact d.Prime := ⟨hd⟩
  haveI : NeZero d := ⟨hd.ne_zero⟩
  -- `↥Q` is abelian
  letI : CommGroup ↥Q :=
    { (inferInstance : Group ↥Q) with
      mul_comm := fun a b => Subtype.ext (hab a.1 a.2 b.1 b.2) }
  -- `V := ↥Q` as a `ZMod d`-module
  have hexpd : ∀ x : Additive ↥Q, d • x = 0 := fun x => by
    obtain ⟨q, rfl⟩ : ∃ q : ↥Q, Additive.ofMul q = x := ⟨x.toMul, rfl⟩
    have hpow : q ^ d = 1 := Subtype.ext (hexp q.1 q.2)
    show d • Additive.ofMul q = 0
    rw [show d • Additive.ofMul q = Additive.ofMul (q ^ d) from rfl, hpow]
    rfl
  -- NB: `haveI` and not `letI`: with `letI`, the local instance keeps an unresolved
  -- `AddCommMonoid (Additive ↥Q)` metavariable in its type and instance search for
  -- `FunLike (Additive ↥Q ≃ₗ[ZMod d] Additive ↥Q) _ _` (hence `CoeFun`) then fails.
  haveI hmod : Module (ZMod d) (Additive ↥Q) := AddCommGroup.zmodModule hexpd
  -- the subgroup of `↥Q` attached to a subspace of `V`
  let SOf : Submodule (ZMod d) (Additive ↥Q) → Subgroup ↥Q := fun W =>
    { carrier := {q : ↥Q | Additive.ofMul q ∈ W}
      mul_mem' := fun {a b} ha hb => by
        show Additive.ofMul (a * b) ∈ W
        rw [show Additive.ofMul (a * b) = Additive.ofMul a + Additive.ofMul b from rfl]
        exact W.add_mem ha hb
      one_mem' := by
        show Additive.ofMul (1 : ↥Q) ∈ W
        rw [show Additive.ofMul (1 : ↥Q) = 0 from rfl]
        exact W.zero_mem
      inv_mem' := fun {a} ha => by
        show Additive.ofMul a⁻¹ ∈ W
        rw [show Additive.ofMul a⁻¹ = -Additive.ofMul a from rfl]
        exact W.neg_mem ha }
  let ROf : Submodule (ZMod d) (Additive ↥Q) → Subgroup G := fun W =>
    (SOf W).map (Subgroup.subtype Q)
  have mem_SOf : ∀ (W : Submodule (ZMod d) (Additive ↥Q)) (q : ↥Q),
      q ∈ SOf W ↔ Additive.ofMul q ∈ W := fun W q => Iff.rfl
  have mem_ROf : ∀ (W : Submodule (ZMod d) (Additive ↥Q)) (q : ↥Q),
      (q : G) ∈ ROf W ↔ q ∈ SOf W := by
    intro W q
    constructor
    · intro h
      obtain ⟨q', hq', hqeq⟩ := Subgroup.mem_map.mp h
      rw [Subtype.ext hqeq] at hq'
      exact hq'
    · intro h
      show (Subgroup.subtype Q) q ∈ (SOf W).map (Subgroup.subtype Q)
      exact Subgroup.mem_map.mpr ⟨q, h, rfl⟩
  have ROf_le : ∀ W : Submodule (ZMod d) (Additive ↥Q), ROf W ≤ Q := fun W => by
    rintro _ ⟨q, -, rfl⟩
    exact q.2
  -- deducing `W = ⊥` and `W = ⊤` from `ROf W = ⊥` and `ROf W = Q`
  have hbot_of : ∀ W : Submodule (ZMod d) (Additive ↥Q), ROf W = ⊥ → W = ⊥ := by
    intro W h
    rw [Submodule.eq_bot_iff]
    intro x hx
    have h1 : x.toMul ∈ SOf W :=
      (mem_SOf W x.toMul).mpr (by rwa [show Additive.ofMul x.toMul = x from rfl])
    have h2 : ((x.toMul : ↥Q) : G) ∈ ROf W := (mem_ROf W x.toMul).mpr h1
    rw [h] at h2
    have h3 : (x.toMul : ↥Q) = 1 := Subtype.ext (Subgroup.mem_bot.mp h2)
    rw [show x = Additive.ofMul (x.toMul : ↥Q) from rfl, h3]
    rfl
  have htop_of : ∀ W : Submodule (ZMod d) (Additive ↥Q), ROf W = Q → W = ⊤ := by
    intro W h
    rw [Submodule.eq_top_iff']
    intro x
    have h1 : ((x.toMul : ↥Q) : G) ∈ ROf W := by rw [h]; exact (x.toMul : ↥Q).2
    have h2 : x.toMul ∈ SOf W := (mem_ROf W x.toMul).mp h1
    have h3 : Additive.ofMul x.toMul ∈ W := (mem_SOf W x.toMul).mp h2
    rwa [show Additive.ofMul x.toMul = x from rfl] at h3
  -- the conjugation action of `U` on `↥Q`
  let nm : U →* MulAut ↥Q :=
    (Subgroup.normalizerMonoidHom (H := Q)).comp (Subgroup.inclusion hUN)
  have nm_val : ∀ (u : U) (x : ↥Q), ((nm u) x : G) = (u : G) * (x : G) * (u : G)⁻¹ := by
    intro u x
    show (((Q.normalizerMonoidHom ((Subgroup.inclusion hUN) u))) x : G) = _
    simp only [Subgroup.normalizerMonoidHom, MulDistribMulAction.toMulAut_apply]
    rfl
  -- the induced `ZMod d`-linear automorphism of `V` (any additive map is `ZMod d`-linear)
  let ρ : U →* (Additive ↥Q ≃ₗ[ZMod d] Additive ↥Q) :=
    { toFun := fun u => ((nm u).toAdditive).toLinearEquiv (fun (c : ZMod d) x => ZMod.map_smul _ c x)
      map_one' := by
        apply LinearEquiv.ext
        intro x
        rw [AddEquiv.coe_toLinearEquiv, map_one nm]
        rw [show (MulEquiv.toAdditive (1 : MulAut ↥Q)) x = Additive.ofMul (Additive.toMul x)
          from rfl]
        rw [show Additive.ofMul (Additive.toMul x) = x from rfl]
        rw [LinearEquiv.one_eq_refl]
        exact (LinearEquiv.refl_apply (R := ZMod d) (M := Additive ↥Q) x).symm
      map_mul' := by
        intro a b
        apply LinearEquiv.ext
        intro x
        rw [LinearEquiv.mul_apply, AddEquiv.coe_toLinearEquiv, AddEquiv.coe_toLinearEquiv,
          AddEquiv.coe_toLinearEquiv]
        rw [show nm (a * b) = nm a * nm b from map_mul nm a b]
        rfl }
  have ρ_apply : ∀ (u : U) (x : ↥Q),
      (ρ u) (Additive.ofMul x) = Additive.ofMul ((nm u) x) := by
    intro u x
    show (((nm u).toAdditive).toLinearEquiv (fun (c : ZMod d) y => ZMod.map_smul _ c y))
      (Additive.ofMul x) = Additive.ofMul ((nm u) x)
    rw [AddEquiv.coe_toLinearEquiv]
    rfl
  -- the kernel of the action is the centralizer of `Q`
  have hnm_one : ∀ u : U, nm u = 1 ↔ (u : G) ∈ Subgroup.centralizer (Q : Set G) := by
    intro u
    constructor
    · intro h
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h3 : (nm u) ⟨y, hy⟩ = ⟨y, hy⟩ := by rw [h]; rfl
      have h4 := nm_val u ⟨y, hy⟩
      rw [h3] at h4
      have h5 : (u : G) * y * (u : G)⁻¹ = y := h4.symm
      calc y * (u : G) = ((u : G) * y * (u : G)⁻¹) * (u : G) := by rw [h5]
        _ = (u : G) * y := by group
    · intro h
      apply MulEquiv.ext
      intro x
      have h2 := (Subgroup.mem_centralizer_iff.mp h) (x : G) x.2
      apply Subtype.ext
      rw [nm_val u x, show (((1 : MulAut ↥Q) x : ↥Q) : G) = (x : G) from rfl]
      rw [← h2]
      group
  have ρ_inj : Function.Injective ρ := by
    intro a b hab
    have hnm : nm a = nm b := by
      ext x
      have h := DFunLike.congr_fun hab (Additive.ofMul x)
      simpa [ρ_apply] using h
    have h1 : nm (a⁻¹ * b) = 1 := by
      rw [map_mul, ← hnm, map_inv, inv_mul_cancel]
    have h2 : ((a⁻¹ * b : U) : G) ∈ Subgroup.centralizer (Q : Set G) :=
      (hnm_one (a⁻¹ * b)).mp h1
    have h3 : ((a⁻¹ * b : U) : G) = 1 := by
      have hmem : ((a⁻¹ * b : U) : G) ∈ U ⊓ Subgroup.centralizer (Q : Set G) :=
        ⟨(a⁻¹ * b).2, h2⟩
      rw [hfaith] at hmem
      exact Subgroup.mem_bot.mp hmem
    have h3' : (a⁻¹ * b : U) = 1 := Subtype.ext h3
    have hb : a * (a⁻¹ * b) = b := by group
    rw [← hb, h3', mul_one]
  -- the images of `U` and `P` in `GL(V)`
  let U' : Subgroup (Additive ↥Q ≃ₗ[ZMod d] Additive ↥Q) := Subgroup.map ρ ⊤
  let PU : P →* U := Subgroup.inclusion hPU
  let P' : Subgroup (Additive ↥Q ≃ₗ[ZMod d] Additive ↥Q) := Subgroup.map (ρ.comp PU) ⊤
  have hcardP' : Nat.card P' = Nat.card P := by
    refine (Nat.card_congr (Equiv.ofBijective
      (fun p : P => (⟨(ρ.comp PU) p, Subgroup.mem_map.mpr ⟨p, Subgroup.mem_top p, rfl⟩⟩ : P'))
      ⟨fun a b hab => ?_, fun y => ?_⟩)).symm
    · have h1 : (ρ.comp PU) a = (ρ.comp PU) b := Subtype.ext_iff.mp hab
      exact Subgroup.inclusion_injective hPU (ρ_inj h1)
    · obtain ⟨p, -, hp⟩ := Subgroup.mem_map.mp y.2
      exact ⟨p, Subtype.ext hp⟩
  have hPU' : P' ≤ U' := by
    rintro x ⟨p, -, rfl⟩
    exact Subgroup.mem_map.mpr ⟨PU p, Subgroup.mem_top _, rfl⟩
  have hPne' : P' ≠ ⊥ := by
    intro h
    have h1 : Nat.card ↥P' = 1 := Subgroup.card_eq_one.mpr h
    have h2 : 1 < Nat.card ↥P := (Subgroup.one_lt_card_iff_ne_bot P).mpr hPne
    rw [hcardP'] at h1
    omega
  -- the fixed-point hypothesis, transferred from the ambient hypothesis
  have hfix' : ∀ P₁ : Subgroup (Additive ↥Q ≃ₗ[ZMod d] Additive ↥Q), P₁ ≤ P' → P₁ ≠ ⊥ →
      Nat.card {v : Additive ↥Q // ∀ u ∈ P₁, u v = v} = Nat.card (ZMod d) := by
    intro P₁ hP₁ hP₁ne
    let P₁₀ : Subgroup G := (Subgroup.comap (ρ.comp PU) P₁).map (Subgroup.subtype P)
    have hP₁₀le : P₁₀ ≤ P := by
      rintro _ ⟨p, -, rfl⟩
      exact p.2
    have hP₁₀ne : P₁₀ ≠ ⊥ := by
      intro h
      apply hP₁ne
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨p, -, rfl⟩ := Subgroup.mem_map.mp (hP₁ hx)
      have hp : (p : G) ∈ P₁₀ := Subgroup.mem_map.mpr ⟨p, hx, rfl⟩
      rw [h] at hp
      have h2 : (p : G) = 1 := Subgroup.mem_bot.mp hp
      have h3 : (p : ↥P) = 1 := Subtype.ext h2
      rw [h3, map_one]
      exact Subgroup.mem_bot.mpr rfl
    have hamb := hfix P₁₀ hP₁₀le hP₁₀ne
    -- fixed vectors of `P₁` are exactly `Q ⊓ C_G(P₁₀)`
    have hbij : {v : Additive ↥Q // ∀ u ∈ P₁, u v = v} ≃
        ↥(Q ⊓ Subgroup.centralizer (P₁₀ : Set G)) := by
      refine Equiv.ofBijective
        (fun v => (⟨((Additive.toMul v.1 : ↥Q) : G),
          Subgroup.mem_inf.mpr ⟨(Additive.toMul v.1).2, ?_⟩⟩ :
            ↥(Q ⊓ Subgroup.centralizer (P₁₀ : Set G))))
        ⟨?_, ?_⟩
      · rw [Subgroup.mem_centralizer_iff]
        intro g hg
        obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hg
        have hv : (ρ (PU p)) (Additive.ofMul (Additive.toMul v.1))
            = Additive.ofMul (Additive.toMul v.1) := by
          change ((ρ.comp PU) p) v.1 = v.1
          exact v.2 _ hp
        have h2 : (nm (PU p)) (Additive.toMul v.1) = Additive.toMul v.1 := by
          rw [ρ_apply (PU p) (Additive.toMul v.1)] at hv
          exact Additive.ofMul.injective hv
        have hx : ((p : G) * ((Additive.toMul v.1 : ↥Q) : G) * (p : G)⁻¹)
            = ((Additive.toMul v.1 : ↥Q) : G) := by
          have h3 : (↑(PU p) * ↑(Additive.toMul v.1) * (↑(PU p))⁻¹ : G)
              = ↑(Additive.toMul v.1) :=
            (nm_val (PU p) (Additive.toMul v.1)).symm.trans
              (congrArg (fun z : ↥Q => (z : G)) h2)
          exact h3
        calc (p : G) * ((Additive.toMul v.1 : ↥Q) : G)
            = (((p : G) * ((Additive.toMul v.1 : ↥Q) : G) * (p : G)⁻¹) * (p : G)) := by
              group
          _ = ((Additive.toMul v.1 : ↥Q) : G) * (p : G) := by rw [hx]
      · rintro ⟨v, hv⟩ ⟨w, hw⟩ heq
        have h2 : ((Additive.toMul v : ↥Q) : G) = ((Additive.toMul w : ↥Q) : G) :=
          congrArg (fun z : ↥(Q ⊓ Subgroup.centralizer (P₁₀ : Set G)) => (z : G)) heq
        have h1 : (Additive.toMul v : ↥Q) = Additive.toMul w := Subtype.ext h2
        apply Subtype.ext
        show Additive.ofMul (Additive.toMul v) = Additive.ofMul (Additive.toMul w)
        rw [h1]
      · intro x
        refine ⟨⟨Additive.ofMul (⟨x.1, x.2.1⟩ : ↥Q), ?_⟩, ?_⟩
        · intro u hu
          obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp (hP₁ hu)
          change (ρ (PU p)) (Additive.ofMul (⟨x.1, x.2.1⟩ : ↥Q))
            = Additive.ofMul (⟨x.1, x.2.1⟩ : ↥Q)
          rw [ρ_apply]
          congr 1
          apply Subtype.ext
          rw [nm_val]
          have hp' : (p : G) ∈ P₁₀ := Subgroup.mem_map.mpr ⟨p, hu, rfl⟩
          have hc : (p : G) * x.1 = x.1 * (p : G) :=
            (Subgroup.mem_centralizer_iff.mp x.2.2) (p : G) hp'
          change (p : G) * x.1 * (p : G)⁻¹ = x.1
          rw [hc]
          group
        · apply Subtype.ext
          rfl
    calc Nat.card {v : Additive ↥Q // ∀ u ∈ P₁, u v = v}
        = Nat.card ↥(Q ⊓ Subgroup.centralizer (P₁₀ : Set G)) := Nat.card_congr hbij
      _ = d := hamb
      _ = Nat.card (ZMod d) := (Nat.card_zmod d).symm
  -- a generator of `T` and the associated `t ∈ U'`
  obtain ⟨t₀, ht₀⟩ := hTcyc.exists_generator
  have hTz : T = Subgroup.zpowers ((t₀ : G)) := by
    apply le_antisymm
    · intro x hx
      have hmem : (⟨x, hx⟩ : ↥T) ∈ Subgroup.zpowers t₀ := ht₀ ⟨x, hx⟩
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      have h2 := map_zpow (Subgroup.subtype T) t₀ k
      exact h2 ▸ congrArg (fun z : ↥T => (z : G)) hk
    · rw [Subgroup.zpowers_le]
      exact t₀.2
  let t : Additive ↥Q ≃ₗ[ZMod d] Additive ↥Q := ρ ⟨(t₀ : G), hTU t₀.2⟩
  have htU' : t ∈ U' := Subgroup.mem_map.mpr ⟨⟨(t₀ : G), hTU t₀.2⟩, Subgroup.mem_top _, rfl⟩
  have t_apply : ∀ x : ↥Q, t (Additive.ofMul x)
      = Additive.ofMul ((nm ⟨(t₀ : G), hTU t₀.2⟩) x) := fun x => ρ_apply _ x
  -- `t` is irreducible on `V`
  have hirr' : ∀ W : Submodule (ZMod d) (Additive ↥Q), (∀ x ∈ W, t x ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    by_cases hT : T = ⊥
    · have hTR : T ≤ Subgroup.normalizer (ROf W : Set G) := by rw [hT]; exact bot_le
      rcases hirr _ (ROf_le W) hTR with h | h
      · exact Or.inl (hbot_of W h)
      · exact Or.inr (htop_of W h)
    · -- `T = ⟨t₀⟩`, and `W` is invariant under `t`, hence `ROf W` under conjugation by `t₀`
      have hconj : ∀ g ∈ ROf W, (t₀ : G) * g * (t₀ : G)⁻¹ ∈ ROf W := by
        intro g hg
        obtain ⟨q, hq, hqeq⟩ := Subgroup.mem_map.mp hg
        have h1 : Additive.ofMul q ∈ W := (mem_SOf W q).mp hq
        have h2 : t (Additive.ofMul q) ∈ W := hW _ h1
        have h3 : Additive.ofMul ((nm ⟨(t₀ : G), hTU t₀.2⟩) q) ∈ W := (t_apply q) ▸ h2
        have h4 : ((nm ⟨(t₀ : G), hTU t₀.2⟩) q : G) ∈ ROf W :=
          (mem_ROf W _).mpr ((mem_SOf W _).mpr h3)
        rw [nm_val] at h4
        rw [← hqeq]
        exact h4
      have ht₀N : (t₀ : G) ∈ Subgroup.normalizer (ROf W : Set G) := by
        rw [Subgroup.mem_normalizer_iff]
        intro x
        exact ⟨fun hx => hconj x hx, fun hx => by
          have hinj : Function.Injective (fun y : ↥(ROf W) =>
              (⟨(t₀ : G) * y.1 * (t₀ : G)⁻¹, hconj y.1 y.2⟩ : ↥(ROf W))) := by
            intro a b hab
            exact Subtype.ext (mul_left_cancel (mul_right_cancel (Subtype.ext_iff.mp hab)))
          obtain ⟨y, hy⟩ := Finite.surjective_of_injective hinj
            (⟨(t₀ : G) * x * (t₀ : G)⁻¹, hx⟩ : ↥(ROf W))
          have h1 : (t₀ : G) * y.1 * (t₀ : G)⁻¹ = (t₀ : G) * x * (t₀ : G)⁻¹ :=
            Subtype.ext_iff.mp hy
          have h2 : y.1 = x := mul_left_cancel (mul_right_cancel h1)
          rw [← h2]
          exact y.2⟩
      have hTR : T ≤ Subgroup.normalizer (ROf W : Set G) := by
        rw [hTz, Subgroup.zpowers_le]
        exact ht₀N
      rcases hirr _ (ROf_le W) hTR with h | h
      · exact Or.inl (hbot_of W h)
      · exact Or.inr (htop_of W h)
  -- `U'` normalizes `⟨t⟩`
  have hnorm' : ∀ u ∈ U', u * t * u⁻¹ ∈ Subgroup.zpowers t := by
    intro u hu
    obtain ⟨u₀, -, rfl⟩ := Subgroup.mem_map.mp hu
    have h1 : (u₀ : G) * (t₀ : G) * (u₀ : G)⁻¹ ∈ T :=
      (Subgroup.mem_normalizer_iff.mp (hUT u₀.2) (t₀ : G)).mp t₀.2
    have hmem : (⟨(u₀ : G) * (t₀ : G) * (u₀ : G)⁻¹, h1⟩ : ↥T) ∈ Subgroup.zpowers t₀ :=
      ht₀ _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hk' : (t₀ : G) ^ k = (u₀ : G) * (t₀ : G) * (u₀ : G)⁻¹ :=
      (map_zpow (Subgroup.subtype T) t₀ k).symm.trans (congrArg (fun z : ↥T => (z : G)) hk)
    have hw : (u₀ * (⟨(t₀ : G), hTU t₀.2⟩ : U) * u₀⁻¹) = (⟨(t₀ : G), hTU t₀.2⟩ : U) ^ k := by
      apply Subtype.ext
      calc (Subgroup.subtype U (u₀ * (⟨(t₀ : G), hTU t₀.2⟩ : U) * u₀⁻¹) : G)
          = (u₀ : G) * (t₀ : G) * (u₀ : G)⁻¹ := by rw [map_mul, map_mul, map_inv]; rfl
        _ = (t₀ : G) ^ k := hk'.symm
        _ = (Subgroup.subtype U ((⟨(t₀ : G), hTU t₀.2⟩ : U) ^ k) : G) := by
              rw [map_zpow]
              rfl
    have hconj : ρ u₀ * t * (ρ u₀)⁻¹ = t ^ k := by
      calc ρ u₀ * t * (ρ u₀)⁻¹
          = ρ u₀ * ρ (⟨(t₀ : G), hTU t₀.2⟩ : U) * (ρ u₀)⁻¹ := rfl
        _ = ρ (u₀ * (⟨(t₀ : G), hTU t₀.2⟩ : U) * u₀⁻¹) := by
              rw [map_mul, map_mul, map_inv]
        _ = ρ ((⟨(t₀ : G), hTU t₀.2⟩ : U) ^ k) := by rw [hw]
        _ = (ρ (⟨(t₀ : G), hTU t₀.2⟩ : U)) ^ k := map_zpow ρ _ k
        _ = t ^ k := rfl
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, hconj.symm⟩
  -- apply the abstract core
  obtain ⟨hprime', hcardV', hcent'⟩ :=
    appVCoreProp (ZMod d) (Additive ↥Q) t hirr' U' htU' hnorm' P' hPU' hPne' hfix'
  refine ⟨?_, ?_, ?_⟩
  · rwa [← hcardP']
  · calc Nat.card Q = Nat.card (Additive ↥Q) := Nat.card_congr Additive.ofMul
      _ = (Nat.card (ZMod d)) ^ Nat.card P' := hcardV'
      _ = d ^ Nat.card P := by rw [Nat.card_zmod, hcardP']
  · intro s hs hs1
    have hsQ : s ∈ Q := (Subgroup.mem_inf.mp hs).1
    have hsC : s ∈ Subgroup.centralizer (P : Set G) := (Subgroup.mem_inf.mp hs).2
    let s' : ↥Q := ⟨s, hsQ⟩
    have hs'ne : s' ≠ 1 := by
      intro h
      exact hs1 (Subtype.ext_iff.mp h)
    have hvne : (Additive.ofMul s' : Additive ↥Q) ≠ 0 := by
      intro h
      apply hs'ne
      have h2 : Additive.toMul (Additive.ofMul s') = Additive.toMul (0 : Additive ↥Q) :=
        congrArg _ h
      rw [show Additive.toMul (Additive.ofMul s') = s' from rfl,
        show Additive.toMul (0 : Additive ↥Q) = 1 from rfl] at h2
      exact h2
    have hvfix : ∀ u ∈ P', u (Additive.ofMul s') = Additive.ofMul s' := by
      rintro u ⟨p, -, rfl⟩
      change (ρ (PU p)) (Additive.ofMul s') = Additive.ofMul s'
      rw [ρ_apply]
      congr 1
      apply Subtype.ext
      rw [nm_val]
      have hc : ((PU p : U) : G) * s = s * ((PU p : U) : G) :=
        (Subgroup.mem_centralizer_iff.mp hsC) ((PU p : U) : G)
          (show ((PU p : U) : G) ∈ P from p.2)
      change ((PU p : U) : G) * s * ((PU p : U) : G)⁻¹ = s
      rw [hc]
      group
    have hmem := hcent' (Additive.ofMul s') hvfix hvne
    refine le_antisymm ?_ ?_
    · rintro u ⟨huU, huC⟩
      have hu' : ρ ⟨u, huU⟩ ∈ U' :=
        Subgroup.mem_map.mpr ⟨⟨u, huU⟩, Subgroup.mem_top _, rfl⟩
      have hfixu : ρ ⟨u, huU⟩ (Additive.ofMul s') = Additive.ofMul s' := by
        rw [ρ_apply]
        congr 1
        apply Subtype.ext
        rw [nm_val]
        have hc : u * s = s * u :=
          ((Subgroup.mem_centralizer_iff.mp huC) s (by simp)).symm
        change u * s * u⁻¹ = s
        rw [hc]
        group
      have hthis := hmem (ρ ⟨u, huU⟩) hu' hfixu
      obtain ⟨p, -, hp⟩ := Subgroup.mem_map.mp hthis
      have hup : PU p = (⟨u, huU⟩ : U) := ρ_inj hp
      have h1 : ((PU p : U) : G) = u := congrArg (fun z : U => (z : G)) hup
      rw [← h1]
      exact p.2
    · intro p hp
      refine ⟨hPU hp, ?_⟩
      exact Subgroup.mem_centralizer_iff.mpr (fun g hg => by
        rw [Set.mem_singleton_iff] at hg
        rw [hg]
        exact ((Subgroup.mem_centralizer_iff.mp hsC) p hp).symm)

end Work.NormalComplement
