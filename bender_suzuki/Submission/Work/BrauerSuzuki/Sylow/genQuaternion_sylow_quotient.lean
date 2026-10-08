import Mathlib
import Submission.Work.BrauerSuzuki.Defs
import Submission.Work.BrauerSuzuki.OddCore.oddCard_oddCore

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Generalized quaternion Sylow 2-subgroups pass to `G / O(G)`

If `S` is a Sylow `2`-subgroup of a finite group `G` and `S` is generalized quaternion, then
the quotient `G ⧸ O(G)` by the largest normal odd-order subgroup has a generalized quaternion
Sylow `2`-subgroup.

The point is that `O(G)` has odd order, so `S ⊓ O(G) = 1`; hence the natural map restricts to
an isomorphism `↥S ≃* ↥(S.map (G → G ⧸ O(G)))`.  By the surjectivity of `G → G ⧸ O(G)`,
`S.map (G → G ⧸ O(G))` is a Sylow `2`-subgroup of the quotient, and `IsGenQuaternion` is
carried across the isomorphism.
-/

set_option autoImplicit false

namespace Work.BrauerSuzuki.Sylow

open Submission.Blueprint

/-- `IsGenQuaternion` is invariant under group isomorphism: push the whole presentation of a
generalized quaternion group forward along `e`. -/
theorem isGenQuaternion_of_mulEquiv {P Q : Type*} [Group P] [Group Q] (e : P ≃* Q)
    (h : Work.BrauerSuzuki.IsGenQuaternion P) :
    Work.BrauerSuzuki.IsGenQuaternion Q := by
  obtain ⟨d⟩ := h
  exact ⟨{
    n := d.n
    hn := d.hn
    tau := e d.tau
    rho := e d.rho
    tau_order := by rw [MulEquiv.orderOf_eq, d.tau_order]
    rho_conj := by
      have := congrArg e d.rho_conj
      simpa only [map_mul, map_inv] using this
    rho_sq := by rw [← map_pow, ← map_pow, d.rho_sq]
    closure_eq_top := by
      rw [show ({e d.tau, e d.rho} : Set Q) = (e : P →* Q) '' ({d.tau, d.rho} : Set P) from by
            ext q; simp,
          ← MonoidHom.map_closure (e : P →* Q), d.closure_eq_top, Subgroup.map_top,
          MonoidHom.range_eq_top.mpr e.surjective]
  }⟩

/-- A Sylow `2`-subgroup meets the odd core `O(G)` trivially: an element of the intersection
has odd order (it lies in `O(G)`, of odd order) and is a `2`-element (it lies in `S`, a
`2`-group). -/
theorem inf_oddCore_eq_bot {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) :
    (S : Subgroup G) ⊓ Submission.Blueprint.oddCore G = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxS, hxO⟩ := hx
  by_contra hxne
  have hodd : Odd (orderOf x) := by
    have hO : Odd (orderOf (⟨x, hxO⟩ : Submission.Blueprint.oddCore G)) :=
      Odd.of_dvd_nat (Work.BrauerSuzuki.OddCore.oddCard_oddCore (G := G))
        (orderOf_dvd_natCard _)
    simpa using hO
  have h2 : 2 ∣ orderOf x := by
    have h1 := S.isPGroup'.dvd_orderOf (g := (⟨x, hxS⟩ : ↥S)) (by
      intro h; exact hxne (Subtype.ext_iff.mp h))
    simpa using h1
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

theorem genQuaternion_sylow_quotient {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hS : Work.BrauerSuzuki.IsGenQuaternion ↥S) :
    ∃ T : Sylow 2 (G ⧸ Submission.Blueprint.oddCore G),
      Work.BrauerSuzuki.IsGenQuaternion ↥T := by
  let O : Subgroup G := Submission.Blueprint.oddCore G
  let π : G →* G ⧸ O := QuotientGroup.mk' O
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective O
  let T : Sylow 2 (G ⧸ O) := Sylow.mapSurjective (p := 2) (f := π) hsurj S
  have hT : (T : Subgroup (G ⧸ O)) = (S : Subgroup G).map π := Sylow.coe_mapSurjective hsurj S
  -- The image of `S` in the quotient.
  let H' : Subgroup (G ⧸ O) := (S : Subgroup G).map π
  -- The restriction of `π` to `S` is injective because `S ⊓ O = ⊥`.
  have hinj : Function.Injective (π.comp (S : Subgroup G).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_bot]
    constructor
    · intro hx
      have hxS : (x : G) ∈ (S : Subgroup G) := x.2
      have hxO : (x : G) ∈ O := by
        have hxker : (x : G) ∈ (QuotientGroup.mk' O).ker := hx
        rwa [QuotientGroup.ker_mk'] at hxker
      have hmem : (x : G) ∈ (S : Subgroup G) ⊓ O := ⟨hxS, hxO⟩
      rw [inf_oddCore_eq_bot S] at hmem
      rw [Subgroup.mem_bot] at hmem
      exact Subtype.ext hmem
    · intro hx
      rw [hx]
      rfl
  -- The induced isomorphism `↥S ≃* ↥H'`.
  let φ : ↥S →* ↥H' := (π.comp (S : Subgroup G).subtype).codRestrict H'
    (fun x => Subgroup.mem_map.mpr ⟨(x : G), x.2, rfl⟩)
  have hφinj : Function.Injective φ := by
    intro x y hxy
    have hπeq : π (x : G) = π (y : G) := by
      have h := congrArg (fun z : ↥H' => (z : G ⧸ O)) hxy
      simp only [φ, MonoidHom.codRestrict_apply] at h
      exact h
    apply Subtype.ext
    have hmem : (x : G) * (y : G)⁻¹ ∈ (S : Subgroup G) ⊓ O := by
      refine ⟨S.mul_mem x.2 (S.inv_mem y.2), ?_⟩
      have hker : (x : G) * (y : G)⁻¹ ∈ (QuotientGroup.mk' O).ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hπeq, mul_inv_cancel]
      rwa [QuotientGroup.ker_mk'] at hker
    rw [inf_oddCore_eq_bot S] at hmem
    rw [Subgroup.mem_bot] at hmem
    exact mul_inv_eq_one.mp hmem
  have hφsurj : Function.Surjective φ := by
    intro y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨x, hx⟩, by
      apply Subtype.ext
      exact hxy⟩
  let e₀ : ↥S ≃* ↥H' := MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  have hgen : Work.BrauerSuzuki.IsGenQuaternion ↥H' := isGenQuaternion_of_mulEquiv e₀ hS
  have hHT : H' = (T : Subgroup (G ⧸ O)) := by rw [hT]
  exact ⟨T, isGenQuaternion_of_mulEquiv (MulEquiv.subgroupCongr hHT) hgen⟩

end Work.BrauerSuzuki.Sylow
