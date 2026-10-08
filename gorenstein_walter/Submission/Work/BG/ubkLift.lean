import Mathlib
import Submission.Work.BG.Hat
import Submission.Work.BG.B_normalizes_K
import Submission.Work.BG.thmCSmallAux
import Submission.Work.BG.b1InfK2EqBot

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16

set_option linter.style.haveILetI false

/-!
# Area BG: lifting characters of the fixed-point subgroup `C_U(s)` to `U` (`U = B ⋊ K`)

At `D.n = 2` (Sylow `2`-subgroup `S` the Klein four group) the hypotheses `ThmCHyps D K1 K2`
give, with `K := K1 ⊓ K2` and `B := C_U(t₁) = C_U(S)`:

* `D.U = D.B ⊔ K` and `D.B ⊓ K = ⊥` (from `D.B1 ⊓ K2 = ⊥`, `b1InfK2EqBot`);
* `K ⊴ U` (`B_normalizes_K` plus `K ≤ N(K)`);
* `C.s = t₁` centralizes `B` and inverts `K`.

Hence `U = B ⋊ K` is a semidirect product with `K` inverted by the involution `s = t₁`, and
the fixed-point subgroup `B_U = Work.BG.fixedSubgroup (Work.BG.sigmaU C)` is exactly the
elements of `U` fixed by (conjugation by) `s = t₁`, i.e. it is `D.B` viewed inside `U`.

`lift_of_involution` below is the abstract step: whenever an involution `σ` of a group `U`
inverts a normal subgroup `K` with `fixedSubgroup σ ⊓ K = ⊥` and `fixedSubgroup σ ⊔ K = ⊤`,
every irreducible character of the fixed-point subgroup extends to an irreducible `σ`-invariant
character of `U` (pull back along `U ⧸ K ≅ fixedSubgroup σ`, `bK ↦ b`).  `ubkLift` and its
`D.B`-form `ubkLiftB` are the instances needed for the `|S| = 4` character analysis.
-/

/-- **Lifting along an inverted normal complement.**  Let `σ` be an automorphism of a group `U`
fixing a subgroup `B = fixedSubgroup σ` elementwise and inverting a normal subgroup `K`; suppose
`B ⊓ K = ⊥` and `B ⊔ K = ⊤`.  Then every irreducible character `β` of `B` extends to an
irreducible character `α` of `U` which is `σ`-invariant and agrees with `β` on `B` (namely
`α := β ∘ ρ` for the projection `ρ : U →* B` with kernel `K`, which satisfies `ρ b = b` for
`b ∈ B`).

The proof only needs `α(σ u) = α(ρ u)`, i.e. `σ u * u⁻¹ ∈ K`; that holds because
`{u | σ u * u⁻¹ ∈ K}` is a subgroup containing `K` (as `σ k * k⁻¹ = k⁻²`) and `B` (as `σ b = b`),
so it contains `B ⊔ K = ⊤`. -/
theorem lift_of_involution {U : Type} [Group U] (σ : MulAut U) (K : Subgroup U)
    (hKn : K.Normal) (hdisj : fixedSubgroup σ ⊓ K = ⊥) (hsup : fixedSubgroup σ ⊔ K = ⊤)
    (hinv : ∀ k ∈ K, σ k = k⁻¹) (β : ClassFunction ↥(fixedSubgroup σ) ℂ)
    (hβ : IsIrreducibleCharacter β) :
    ∃ α : ClassFunction U ℂ, IsIrreducibleCharacter α ∧ (∀ u, α (σ u) = α u) ∧
      ∀ c : ↥(fixedSubgroup σ), α (c : U) = β c := by
  classical
  haveI := hKn
  have hH : ∀ u : U, σ u * u⁻¹ ∈ K := by
    let H : Subgroup U :=
      { carrier := {u | σ u * u⁻¹ ∈ K}
        one_mem' := by simp
        mul_mem' := by
          intro a b ha hb
          change σ a * a⁻¹ ∈ K at ha
          change σ b * b⁻¹ ∈ K at hb
          change σ (a * b) * (a * b)⁻¹ ∈ K
          have key : σ (a * b) * (a * b)⁻¹ = (σ a * a⁻¹) * (a * (σ b * b⁻¹) * a⁻¹) := by
            rw [map_mul]
            group
          rw [key]
          exact K.mul_mem ha (hKn.conj_mem (σ b * b⁻¹) hb a)
        inv_mem' := by
          intro a ha
          change σ a * a⁻¹ ∈ K at ha
          show σ a⁻¹ * (a⁻¹)⁻¹ ∈ K
          have key : σ a⁻¹ * (a⁻¹)⁻¹ = a⁻¹ * (σ a * a⁻¹)⁻¹ * (a⁻¹)⁻¹ := by
            rw [map_inv, show σ a = (σ a * a⁻¹) * a from by group]
            group
          rw [key]
          exact hKn.conj_mem (σ a * a⁻¹)⁻¹ (K.inv_mem ha) a⁻¹ }
    have hKle : K ≤ H := by
      intro k hk
      change σ k * k⁻¹ ∈ K
      rw [hinv k hk]
      exact K.mul_mem (K.inv_mem hk) (K.inv_mem hk)
    have hBle : fixedSubgroup σ ≤ H := by
      intro c hc
      change σ c * c⁻¹ ∈ K
      rw [mem_fixedSubgroup.mp hc]
      simp
    have htop : H = ⊤ := by
      rw [eq_top_iff, ← hsup]
      exact sup_le hBle hKle
    intro u
    exact le_of_eq htop.symm (Subgroup.mem_top u)
  let ψ : ↥(fixedSubgroup σ) →* U ⧸ K := (QuotientGroup.mk' K).comp (fixedSubgroup σ).subtype
  have hψinj : Function.Injective ψ := by
    intro a b hab
    change QuotientGroup.mk' K (a : U) = QuotientGroup.mk' K (b : U) at hab
    have hmem : (a : U) * (b : U)⁻¹ ∈ K := by
      have h1 : QuotientGroup.mk' K ((a : U) * (b : U)⁻¹) = 1 := by
        rw [map_mul, map_inv, hab, mul_inv_cancel]
      exact (QuotientGroup.eq_one_iff _).mp h1
    have hmemB : (a : U) * (b : U)⁻¹ ∈ fixedSubgroup σ :=
      (fixedSubgroup σ).mul_mem a.2 ((fixedSubgroup σ).inv_mem b.2)
    have hone : (a : U) * (b : U)⁻¹ = 1 := by
      have h := Subgroup.mem_inf.mpr ⟨hmemB, hmem⟩
      rw [hdisj] at h
      exact Subgroup.mem_bot.mp h
    exact Subtype.ext (mul_inv_eq_one.mp hone)
  have hψsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective K y
    have hxu : u ∈ fixedSubgroup σ ⊔ K := le_of_eq hsup.symm (Subgroup.mem_top u)
    obtain ⟨b, hb, k, hk, hbk⟩ :=
      (Subgroup.mem_sup_of_normal_right (s := fixedSubgroup σ) (t := K)).mp hxu
    have hk1 : (QuotientGroup.mk' K) k = 1 := (QuotientGroup.eq_one_iff k).mpr hk
    refine ⟨⟨b, hb⟩, ?_⟩
    change QuotientGroup.mk' K b = QuotientGroup.mk' K u
    rw [← hbk, map_mul, hk1, mul_one]
  let e : ↥(fixedSubgroup σ) ≃* U ⧸ K := MulEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩
  have he_apply : ∀ b : ↥(fixedSubgroup σ), e b = QuotientGroup.mk' K (b : U) := fun b => rfl
  let ρ : U →* ↥(fixedSubgroup σ) := e.symm.toMonoidHom.comp (QuotientGroup.mk' K)
  have hρ_apply : ∀ u : U, ρ u = e.symm (QuotientGroup.mk' K u) := fun u => rfl
  have hρsurj : Function.Surjective ρ := by
    intro b
    refine ⟨(b : U), ?_⟩
    rw [hρ_apply, ← he_apply b, MulEquiv.symm_apply_apply]
  refine ⟨ClassFunction.compHom ρ β, ?_, ?_, ?_⟩
  · exact IsIrreducibleCharacter.compHom_of_surjective hρsurj hβ
  · intro u
    have hq : QuotientGroup.mk' K (σ u) = QuotientGroup.mk' K u := by
      have h3 : QuotientGroup.mk' K (σ u * u⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr (hH u)
      rw [map_mul, map_inv] at h3
      exact mul_inv_eq_one.mp h3
    simp only [ClassFunction.compHom_apply]
    rw [hρ_apply, hρ_apply, hq]
  · intro c
    simp only [ClassFunction.compHom_apply]
    have hρc : ρ (c : U) = c := by
      rw [hρ_apply, ← he_apply c, MulEquiv.symm_apply_apply]
    rw [hρc]

/-- At `D.n = 2` (Sylow `2`-subgroup `S` the Klein four group) the hypotheses `ThmCHyps D K1 K2` give, with `K := K1 ⊓ K2` and `B := C_U(t₁) = C_U(S)`: `D.U = D.B ⊔ K`, `D.B ⊓ K = ⊥`, `K ⊴ U`, and `C.s = t₁` centralizes `B` and inverts `K`.  Hence `U = B ⋊ K`, and every irreducible character `β` of the fixed-point subgroup `B_U := Work.BG.fixedSubgroup (Work.BG.sigmaU C)` (the elements of `U` fixed by conjugation by `s = t₁`) lifts to an irreducible character of `U` which is `s`-invariant and agrees with `β` on `B_U`.  Concretely `α₁ := β ∘ e` where `e : U → U/K ≅ B_U` is inverse to `b ↦ bK`.  NOTE (import clash): do NOT import `Submission.Work.BG.kEqSmall`, `Submission.Work.BG.b1InfK2EqBot` or `Submission.Work.BG.thmCSmallShape`: they declare `Work.BG.eq_of_orderOf_eq_two_of_isCyclic`, which clashes with the copy pulled in by `Submission.Work.BG.HatInjDefs` (via `S_le_H`); the ingredient `D.B1 ⊓ K2 = ⊥` must be reproved locally (proof in `b1InfK2EqBot.lean`, see also `kEqSmallAlt.lean`). -/
theorem ubkLift {G : Type} [Group G] [Finite G]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) (K1 K2 : Subgroup G)
    (hc : Work.GW2.C16.Compat D C) (hn : D.n = 2) (hT : Work.GW2.C16.ThmCHyps D K1 K2)
    (β : ClassFunction ↥(Work.BG.fixedSubgroup (Work.BG.sigmaU C)) ℂ)
    (hβ : IsIrreducibleCharacter β) :
    ∃ α₁ : ClassFunction ↥C.P.U ℂ,
      IsIrreducibleCharacter α₁ ∧
      (∀ u : ↥C.P.U, α₁ (Work.BG.sigmaU C u) = α₁ u) ∧
      (∀ c : ↥(Work.BG.fixedSubgroup (Work.BG.sigmaU C)), α₁ (c : ↥C.P.U) = β c) := by
  obtain ⟨h1, h2, hdir, -, -, -⟩ := hT
  -- `B₁ ⊓ K₂ = ⊥`, so the direct decomposition of `ThmCHyps` collapses to `U = B K`.
  have hA : D.B1 ⊓ K2 = ⊥ := b1InfK2EqBot D K2 hn h2
  have hUeq : D.U = D.B ⊔ (K1 ⊓ K2) := by
    have h := hdir.1
    rw [hA, bot_sup_eq] at h
    exact h.symm
  have hKleU : (K1 ⊓ K2 : Subgroup G) ≤ C.P.U := by
    rw [hc.U_eq, hUeq]
    exact le_sup_right
  -- `K = K₁ ⊓ K₂` is normal in `U = B K`: `B` normalizes `K` and `K` normalizes itself.
  have hKnorm : ((K1 ⊓ K2 : Subgroup G).subgroupOf C.P.U).Normal := by
    have hBnorm : D.B ≤ Subgroup.normalizer ((K1 ⊓ K2 : Subgroup G) : Set G) :=
      Subgroup.le_normalizer_iff_commutator_le_right.mpr (B_normalizes_K D K1 K2 h1 h2)
    have hUnorm : C.P.U ≤ Subgroup.normalizer ((K1 ⊓ K2 : Subgroup G) : Set G) := by
      rw [hc.U_eq, hUeq]
      exact sup_le hBnorm (Subgroup.le_normalizer)
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hKleU).mpr hUnorm
  -- the fixed-point subgroup of `sigmaU C` is `B` (inside `U`), and `B ⊓ K = ⊥`.
  have hdisj : fixedSubgroup (sigmaU C) ⊓ (K1 ⊓ K2).subgroupOf C.P.U = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxfix, hxK⟩ := hx
    have hxB : ((x : ↥C.P.U) : G) ∈ D.B := hatInjBIdent C hc hn x hxfix
    have hxK2 : ((x : ↥C.P.U) : G) ∈ K2 := (Subgroup.mem_subgroupOf.mp hxK).2
    have hmem : ((x : ↥C.P.U) : G) ∈ D.B1 ⊓ K2 := ⟨hxB.1, hxK2⟩
    rw [hA] at hmem
    exact Subtype.ext (by simpa using Subgroup.mem_bot.mp hmem)
  -- `U = B K`, as subgroups of `U`.
  have hsup : fixedSubgroup (sigmaU C) ⊔ (K1 ⊓ K2).subgroupOf C.P.U = ⊤ := by
    have hImage : D.U ≤
        (fixedSubgroup (sigmaU C) ⊔ (K1 ⊓ K2).subgroupOf C.P.U).map C.P.U.subtype := by
      rw [hUeq]
      refine sup_le ?_ ?_
      · intro b hb
        refine Subgroup.mem_map.mpr ⟨⟨b, hc.U_eq ▸ mem_DU_of_mem_B D hb⟩, ?_, rfl⟩
        exact Subgroup.mem_sup_left
          (sigmaU_eq_self_of_mem_B D C hc hb (hc.U_eq ▸ mem_DU_of_mem_B D hb))
      · intro k hk
        refine Subgroup.mem_map.mpr ⟨⟨k, hKleU hk⟩, ?_, rfl⟩
        exact Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mpr hk)
    rw [eq_top_iff]
    intro x _
    have hx : ((x : ↥C.P.U) : G) ∈
        (fixedSubgroup (sigmaU C) ⊔ (K1 ⊓ K2).subgroupOf C.P.U).map C.P.U.subtype :=
      hImage (hc.U_eq ▸ x.2)
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    have heq : y = x := Subtype.ext hyx
    rw [heq] at hy
    exact hy
  -- `s = t₁` inverts `K ≤ K₁`.
  have hinv : ∀ k ∈ (K1 ⊓ K2).subgroupOf C.P.U, sigmaU C k = k⁻¹ := by
    intro k hk
    apply Subtype.ext
    have hk1 : ((k : ↥C.P.U) : G) ∈ K1 := (Subgroup.mem_subgroupOf.mp hk).1
    rw [sigmaU_apply_coe, hc.s_eq]
    exact h1.2.2.1 _ hk1
  exact lift_of_involution (sigmaU C) ((K1 ⊓ K2).subgroupOf C.P.U) hKnorm hdisj hsup hinv β hβ

/-- **`ubkLift` in terms of `D.B`.**  Same conclusion as `ubkLift`, but for an irreducible
character `θ` of `B = D.B = C_U(t₁) = C_U(S)` (rather than of `B_U = fixedSubgroup (sigmaU C)`,
to which `D.B` is carried by `hatEquiv`): the lift `α₁` agrees with `θ` on `B`. -/
theorem ubkLiftB {G : Type} [Group G] [Finite G]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) (K1 K2 : Subgroup G)
    (hc : Work.GW2.C16.Compat D C) (hn : D.n = 2) (hT : Work.GW2.C16.ThmCHyps D K1 K2)
    (θ : ClassFunction ↥D.B ℂ) (hθ : IsIrreducibleCharacter θ) :
    ∃ α₁ : ClassFunction ↥C.P.U ℂ,
      IsIrreducibleCharacter α₁ ∧
      (∀ u : ↥C.P.U, α₁ (sigmaU C u) = α₁ u) ∧
      (∀ b : ↥D.B, α₁ ⟨(b : G), hc.U_eq ▸ mem_DU_of_mem_B D b.2⟩ = θ b) := by
  have hβ : IsIrreducibleCharacter
      (ClassFunction.compHom (hatEquiv D C hc hn).toMonoidHom θ) :=
    IsIrreducibleCharacter.compHom_of_surjective (hatEquiv D C hc hn).surjective hθ
  obtain ⟨α₁, hirr, hinv, hres⟩ :=
    ubkLift D C K1 K2 hc hn hT
      (ClassFunction.compHom (hatEquiv D C hc hn).toMonoidHom θ) hβ
  refine ⟨α₁, hirr, hinv, ?_⟩
  intro b
  have hsymm : ((hatEquiv D C hc hn).symm b : ↥C.P.U)
      = ⟨(b : G), hc.U_eq ▸ mem_DU_of_mem_B D b.2⟩ :=
    Subtype.ext (hatEquiv_symm_coe D C hc hn b)
  have h := hres ((hatEquiv D C hc hn).symm b)
  rw [hsymm] at h
  rw [h]
  exact congrArg θ (MulEquiv.apply_symm_apply (hatEquiv D C hc hn) b)

end Work.BG
