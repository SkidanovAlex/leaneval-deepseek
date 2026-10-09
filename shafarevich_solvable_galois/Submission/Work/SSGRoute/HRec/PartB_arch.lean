/-
# Part B, node B7: at `p = 2` the archimedean pairing is the indicator of the local cup class

`HRec/HRECJOINT_DESIGN.md` (node `B7`).  For `p = 2` and an involution `σ`, the archimedean
pairing `Ach.archPair` — hence `E7Arch.pairArchFamily` at `Subgroup.zpowers σ` — is nonzero exactly
when the local cup class of `evCupFun a b` in `H²(⟨σ⟩, μ₂)` is nonzero:

`archPair σ a b = if evCupFun a b ∈ coboundaries2 ⟨σ⟩ then 0 else 1`.

The point is that for `p = 2` the coefficient module `μ₂ ≅ DualMod p T` is a *line over 𝔽₂*, so its
`Gal`-action is trivial (`smul_eq_self_of_finrank_eq_one`, `smul_dualMod_eq_self`); the
coboundary condition on the two-element group `⟨σ⟩` then reduces to "all four values vanish", and
the cup cochain is the value `evLin (a σ ⊗ b σ)`, whose only invariant is its value at the
generator `t0` of `T`.  That value is exactly `b σ (a σ ⊗₀ t0)` = `archPair σ a b`.

This replaces the *stale* draft statement of B7, which used the dropped `HRec.classOf`; the "class
is zero" test is `∈ coboundaries2`, exactly as in `Parity2`.
-/
import Mathlib
import Submission.Work.SSGRoute.HRec.HrecDefs
import Submission.Work.SSGRoute.HRec.PartB_nondeg
import Submission.Work.SSGRoute.E7Arch.pairFamily
import Submission.Work.SSGRoute.LTDArch.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open SSGRoute
open Classical
open scoped TensorProduct

namespace Work.SSGRoute.HRec

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
  (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
  (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)

/-- For `p = 2` a rank-one module carries the trivial action. -/
theorem smul_eq_self_of_finrank_eq_one (hp : p = 2) (h1 : Module.finrank (ZMod p) T = 1)
    (g : K ≃ₐ[k] K) (t : T) : g • t = t := by
  have hcoord : Ach.coord p T h1 (g • Ach.t0 p T h1) = 1 := by
    refine eq_one_of_ne_zero_of_eq_two p hp ?_
    intro hz
    have hzero : g • Ach.t0 p T h1 = 0 := by
      rw [← Ach.smul_coord_t0 p T h1 (g • Ach.t0 p T h1), hz, zero_smul]
    have hne : g • Ach.t0 p T h1 ≠ 0 := by
      intro h
      have h' : g⁻¹ • (g • Ach.t0 p T h1) = Ach.t0 p T h1 := inv_smul_smul g _
      rw [h, smul_zero] at h'
      exact Ach.t0_ne_zero p T h1 h'.symm
    exact hne hzero
  calc g • t = g • (Ach.coord p T h1 t • Ach.t0 p T h1) := by rw [Ach.smul_coord_t0]
    _ = Ach.coord p T h1 t • (g • Ach.t0 p T h1) := by rw [smul_comm]
    _ = Ach.coord p T h1 t • Ach.t0 p T h1 := by
          rw [← Ach.smul_coord_t0 p T h1 (g • Ach.t0 p T h1), hcoord, one_smul]
    _ = t := Ach.smul_coord_t0 p T h1 t

/-- For `p = 2` the dual of a rank-one module carries the trivial action. -/
theorem smul_dualMod_eq_self (hp : p = 2) (h1 : Module.finrank (ZMod p) T = 1)
    (g : K ≃ₐ[k] K) (f : Work.SSGRoute.DualMod p T) : g • f = f := by
  ext t
  rw [DualMod.dualSMul_apply,
    smul_eq_self_of_finrank_eq_one p k Ω K T hp h1 g⁻¹ t]

/-- **The archimedean pairing at an involution, for `p = 2`**, is the indicator of the local cup
class on `⟨σ⟩`. -/
theorem archPair_eq_indicator_two (hp : p = 2) (σ : Ω ≃ₐ[k] Ω) (hσ : σ ^ 2 = 1)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))
    (ha1 : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ a) (ha2 : SSGRoute.IsLocConstOn ⊤ a)
    (hb1 : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b) (hb2 : SSGRoute.IsLocConstOn ⊤ b) :
    Ach.archPair p (Ω ≃ₐ[k] Ω) M T hT.1 σ a b =
      if Work.SSGRoute.E7Fin.evCupFun p k Ω K T M a b ∈
          Work.SSGRoute.coboundaries2 p k Ω K (Work.SSGRoute.DualMod p T) (Subgroup.zpowers σ)
        then 0 else 1 := by
  classical
  set cN : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p T :=
    Work.SSGRoute.E7Fin.evCupFun p k Ω K T M a b with hcNdef
  -- the two `1`-cocycle identities
  have ha_one : a 1 = 0 := by
    have h := ha1 1 (Subgroup.mem_top 1) 1 (Subgroup.mem_top 1)
    rw [mul_one, map_one, one_smul] at h
    exact (add_left_cancel (a := a 1) (b := 0) (c := a 1)
      (by rw [add_zero]; exact h)).symm
  have hb_one : b 1 = 0 := by
    have h := hb1 1 (Subgroup.mem_top 1) 1 (Subgroup.mem_top 1)
    rw [mul_one, map_one, one_smul] at h
    exact (add_left_cancel (a := b 1) (b := 0) (c := b 1)
      (by rw [add_zero]; exact h)).symm
  have hσa : SSGRoute.res k K σ • a σ = a σ := by
    have h := ha1 σ (Subgroup.mem_top σ) σ (Subgroup.mem_top σ)
    rw [← pow_two, hσ, ha_one] at h
    have h' : SSGRoute.res k K σ • a σ + a σ = 0 := by rw [add_comm]; exact h.symm
    have hneg : SSGRoute.res k K σ • a σ = -(a σ) := by
      rw [eq_neg_iff_add_eq_zero]; exact h'
    rw [hneg, Ach.neg_eq_self_of_eq_two p hp]
  have hσb : SSGRoute.res k K σ • b σ = b σ := by
    have h := hb1 σ (Subgroup.mem_top σ) σ (Subgroup.mem_top σ)
    rw [← pow_two, hσ, hb_one] at h
    have h' : SSGRoute.res k K σ • b σ + b σ = 0 := by rw [add_comm]; exact h.symm
    have hneg : SSGRoute.res k K σ • b σ = -(b σ) := by
      rw [eq_neg_iff_add_eq_zero]; exact h'
    rw [hneg, Ach.neg_eq_self_of_eq_two p hp]
  -- the values of the cup cochain on `⟨σ⟩ × ⟨σ⟩`
  have hcN11 : cN 1 1 = 0 := by
    rw [hcNdef]
    simp [Work.SSGRoute.E7Fin.evCupFun_apply, ha_one]
  have hcN1σ : cN 1 σ = 0 := by
    rw [hcNdef]
    simp [Work.SSGRoute.E7Fin.evCupFun_apply, ha_one]
  have hcNσ1 : cN σ 1 = 0 := by
    rw [hcNdef]
    simp [Work.SSGRoute.E7Fin.evCupFun_apply, hb_one]
  have hcNσσ : cN σ σ = Work.SSGRoute.E7Fin.evLin p M T
      (TensorProduct.tmul (ZMod p) (a σ) (b σ)) := by
    rw [hcNdef]
    simp [Work.SSGRoute.E7Fin.evCupFun_apply, hσb]
  have hcNt0 : (cN σ σ) (Ach.t0 p T hT.1) =
      b σ (TensorProduct.tmul (ZMod p) (a σ) (Ach.t0 p T hT.1)) := by
    rw [hcNσσ, Work.SSGRoute.E7Fin.evLin_tmul]
    rfl
  -- a functional on the line `DualMod p T` vanishes iff it vanishes at `t0`
  have hdual : ∀ f : Work.SSGRoute.DualMod p T, f = 0 ↔ f (Ach.t0 p T hT.1) = 0 := by
    intro f
    constructor
    · intro h
      rw [h]
      rfl
    · intro h
      ext t
      calc f t = f ((Ach.coord p T hT.1 t) • Ach.t0 p T hT.1) := by
              rw [Ach.smul_coord_t0]
        _ = (Ach.coord p T hT.1 t) • f (Ach.t0 p T hT.1) := by rw [map_smul]
        _ = 0 := by rw [h, smul_zero]
  -- the coboundary criterion on `⟨σ⟩`
  have hcob : cN ∈ Work.SSGRoute.coboundaries2 p k Ω K (Work.SSGRoute.DualMod p T)
      (Subgroup.zpowers σ) ↔ cN σ σ = 0 := by
    constructor
    · rintro ⟨b', _hb'loc, hb'eq⟩
      have hb'1 : b' 1 = 0 := by
        have h1 := hb'eq 1 (Subgroup.one_mem _) 1 (Subgroup.one_mem _)
        rw [mul_one, map_one, one_smul, hcN11] at h1
        simpa using h1.symm
      have h2 := hb'eq σ (Subgroup.mem_zpowers σ) σ (Subgroup.mem_zpowers σ)
      rw [show σ * σ = 1 from by rw [← pow_two, hσ], hb'1, sub_zero,
        smul_dualMod_eq_self p k Ω K T hp hT.1 (SSGRoute.res k K σ) (b' σ),
        Ach.add_self_eq_zero_of_eq_two p hp (b' σ)] at h2
      exact h2
    · intro h
      refine ⟨fun _ => 0, ⟨⊤, isOpen_univ, fun g _ u _ _ => rfl⟩, ?_⟩
      intro g hg h' hh
      rcases Ach.mem_zpowers_eq_one_or σ hσ hg with hg1 | hgσ
      · rcases Ach.mem_zpowers_eq_one_or σ hσ hh with hh1 | hhσ
        · simp only [hg1, hh1, map_zero, smul_zero, sub_zero, add_zero]; exact hcN11
        · simp only [hg1, hhσ, map_zero, smul_zero, sub_zero, add_zero]; exact hcN1σ
      · rcases Ach.mem_zpowers_eq_one_or σ hσ hh with hh1 | hhσ
        · simp only [hgσ, hh1, map_zero, smul_zero, sub_zero, add_zero]; exact hcNσ1
        · simp only [hgσ, hhσ, map_zero, smul_zero, sub_zero, add_zero]; exact h
  rw [Ach.archPair_apply_of_eq_two p (Ω ≃ₐ[k] Ω) M T hp σ a b]
  rw [← hcNt0]
  by_cases hmem : cN ∈ Work.SSGRoute.coboundaries2 p k Ω K (Work.SSGRoute.DualMod p T)
      (Subgroup.zpowers σ)
  · rw [if_pos hmem, hcob.mp hmem]
    simp
  · rw [if_neg hmem]
    refine eq_one_of_ne_zero_of_eq_two p hp ?_
    intro hz
    exact hmem (hcob.mpr ((hdual (cN σ σ)).mpr hz))

/-- **B7 (`pairArchFamily_eq_indicator_two`)**: for `p = 2` the archimedean family at the subgroup
generated by an involution is the indicator of the local cup class. -/
theorem pairArchFamily_eq_indicator_two (hp : p = 2)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))
    (ha1 : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ a) (ha2 : SSGRoute.IsLocConstOn ⊤ a)
    (hb1 : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b) (hb2 : SSGRoute.IsLocConstOn ⊤ b)
    (c : Ω ≃ₐ[k] Ω) (hc : c ^ 2 = 1) :
    Work.SSGRoute.E7Arch.pairArchFamily p k Ω K ζ hζ hζK T hT M (Subgroup.zpowers c) a b =
      if Work.SSGRoute.E7Fin.evCupFun p k Ω K T M a b ∈
          Work.SSGRoute.coboundaries2 p k Ω K (Work.SSGRoute.DualMod p T) (Subgroup.zpowers c)
        then 0 else 1 := by
  rw [Work.SSGRoute.E7Arch.pairArchFamily_zpowers_apply,
    ← Work.SSGRoute.E7Arch.zpowers_genArch p k Ω K ζ hζ hζK T hT c hc]
  exact archPair_eq_indicator_two p k Ω K ζ T hT hp
    (Work.SSGRoute.E7Arch.genArch p k Ω K ζ hζ hζK T hT c hc)
    (Work.SSGRoute.E7Arch.genArch_sq p k Ω K ζ hζ hζK T hT c hc)
    M a b ha1 ha2 hb1 hb2

end Work.SSGRoute.HRec
