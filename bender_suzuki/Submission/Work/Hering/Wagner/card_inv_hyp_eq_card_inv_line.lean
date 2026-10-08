import Mathlib
import Submission.Work.Hering.Wagner.card_hyp_above
import Submission.Work.Hering.Wagner.zmod2_dual_ker_injective
import Submission.Work.Hering.Wagner.exists_dual_ker_eq

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.Wagner

/-- Over `ZMod 2`, a nonzero scalar is `1`. -/
private lemma zmod2_eq_one_of_ne_zero {c : ZMod 2} (hc : c ≠ 0) : c = 1 := by
  fin_cases c
  · exact absurd rfl hc
  · rfl

/-- Over `𝔽₂`, a one-dimensional subspace `P` is `T`-invariant if and only if it is contained
in the `1`-eigenspace of `T`. -/
theorem line_invariant_iff_le_ker {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    [Module.Finite (ZMod 2) W] (T : W ≃ₗ[ZMod 2] W) (P : Submodule (ZMod 2) W)
    (hP : Module.finrank (ZMod 2) P = 1) :
    P.map (T : W →ₗ[ZMod 2] W) = P ↔
      P ≤ LinearMap.ker ((T : W →ₗ[ZMod 2] W) - 1) := by
  constructor
  · intro h x hx
    obtain ⟨v, hv, hgen⟩ := finrank_eq_one_iff'.1 hP
    have hTW : T (v : W) ∈ P := by
      have hmem : T (v : W) ∈ P.map (T : W →ₗ[ZMod 2] W) := Submodule.mem_map_of_mem v.2
      rwa [h] at hmem
    obtain ⟨c, hc⟩ := hgen ⟨T (v : W), hTW⟩
    have hc' : c • (v : W) = (T : W →ₗ[ZMod 2] W) (v : W) := by
      simpa using congrArg Subtype.val hc
    have hvW : (v : W) ≠ 0 := fun h0 => hv (Subtype.ext h0)
    have hc_ne : c ≠ 0 := by
      intro hc0
      rw [hc0, zero_smul] at hc'
      exact hvW (T.injective (by simpa using hc'.symm))
    have hTv : (T : W →ₗ[ZMod 2] W) (v : W) = (v : W) := by
      rw [← hc', zmod2_eq_one_of_ne_zero hc_ne, one_smul]
    obtain ⟨d, hd⟩ := hgen ⟨x, hx⟩
    have hd' : d • (v : W) = x := by simpa using congrArg Subtype.val hd
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    rw [← hd', map_smul, hTv]
  · intro h
    apply le_antisymm
    · rintro y hy
      obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
      have hz' : z ∈ LinearMap.ker ((T : W →ₗ[ZMod 2] W) - 1) := h hz
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hz'
      rwa [hz']
    · intro x hx
      rw [Submodule.mem_map]
      have hx' : x ∈ LinearMap.ker ((T : W →ₗ[ZMod 2] W) - 1) := h hx
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hx'
      exact ⟨x, hx, hx'⟩

/-- Over `𝔽₂`, a hyperplane `H` is `T`-invariant if and only if it contains the image of `T - 1`. -/
theorem hyp_invariant_iff_range_le {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    [Module.Finite (ZMod 2) W] (T : W ≃ₗ[ZMod 2] W) (H : Submodule (ZMod 2) W)
    (hH : Module.finrank (ZMod 2) H + 1 = Module.finrank (ZMod 2) W) :
    H.map (T : W →ₗ[ZMod 2] W) = H ↔
      LinearMap.range ((T : W →ₗ[ZMod 2] W) - 1) ≤ H := by
  set f : W →ₗ[ZMod 2] W := (T : W →ₗ[ZMod 2] W) with hf
  constructor
  · intro h
    have hpos : 0 < Module.finrank (ZMod 2) W := by omega
    have hfin : Module.finrank (ZMod 2) H = Module.finrank (ZMod 2) W - 1 := by omega
    obtain ⟨φ, hφne, hφker⟩ := exists_dual_ker_eq hpos H hfin
    have hcomap : H.comap f = H := by
      apply le_antisymm
      · intro y hy
        rw [Submodule.mem_comap] at hy
        have hy' : f y ∈ H.map f := by rw [h]; exact hy
        obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.mp hy'
        have hzy' : z = y := T.injective hzy
        rw [hzy'] at hz
        exact hz
      · intro y hy
        rw [Submodule.mem_comap, ← h]
        exact Submodule.mem_map_of_mem hy
    have hkerT : LinearMap.ker (f.dualMap φ) = H.comap f := by
      ext x
      rw [LinearMap.mem_ker, LinearMap.dualMap_apply, Submodule.mem_comap, ← hφker,
        LinearMap.mem_ker]
    have hfix : f.dualMap φ = φ := by
      refine zmod2_dual_ker_injective ?_ hφne ?_
      · intro h0
        exact hφne (LinearMap.dualMap_injective_of_surjective T.surjective (by rw [h0, map_zero]))
      · rw [hkerT, hcomap, hφker]
    rintro y ⟨x, rfl⟩
    have hval : φ ((f - 1) x) = 0 := by
      have h1 : φ (f x) = φ x := by rw [← LinearMap.dualMap_apply f φ x, hfix]
      simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, h1, sub_self]
    have : (f - 1) x ∈ LinearMap.ker φ := LinearMap.mem_ker.mpr hval
    rwa [hφker] at this
  · intro h
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rintro y hy
      obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
      have hz1 : f z - z ∈ H := by
        have := h ⟨z, rfl⟩
        rwa [LinearMap.sub_apply, Module.End.one_apply] at this
      have : f z - z + z ∈ H := H.add_mem hz1 hz
      rwa [sub_add_cancel] at this
    · exact LinearEquiv.finrank_map_eq T H

theorem card_inv_hyp_eq_card_inv_line {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    [Module.Finite (ZMod 2) W] (T : W ≃ₗ[ZMod 2] W) :
    Nat.card {H : Submodule (ZMod 2) W //
        Module.finrank (ZMod 2) H + 1 = Module.finrank (ZMod 2) W ∧
          H.map (T : W →ₗ[ZMod 2] W) = H}
      = Nat.card {P : Submodule (ZMod 2) W //
        Module.finrank (ZMod 2) P = 1 ∧
          P.map (T : W →ₗ[ZMod 2] W) = P} := by
  classical
  have eA : {H : Submodule (ZMod 2) W //
        Module.finrank (ZMod 2) H + 1 = Module.finrank (ZMod 2) W ∧
          H.map (T : W →ₗ[ZMod 2] W) = H}
      ≃ {H : Submodule (ZMod 2) W //
        LinearMap.range ((T : W →ₗ[ZMod 2] W) - 1) ≤ H ∧
          Module.finrank (ZMod 2) H + 1 = Module.finrank (ZMod 2) W} :=
    Equiv.subtypeEquivRight fun H =>
      ⟨fun ⟨h1, h2⟩ => ⟨(hyp_invariant_iff_range_le T H h1).mp h2, h1⟩,
       fun ⟨h1, h2⟩ => ⟨h2, (hyp_invariant_iff_range_le T H h2).mpr h1⟩⟩
  have hA : Nat.card {H : Submodule (ZMod 2) W //
        Module.finrank (ZMod 2) H + 1 = Module.finrank (ZMod 2) W ∧
          H.map (T : W →ₗ[ZMod 2] W) = H}
      = 2 ^ (Module.finrank (ZMod 2) W -
            Module.finrank (ZMod 2) ↥(LinearMap.range ((T : W →ₗ[ZMod 2] W) - 1))) - 1 := by
    rw [Nat.card_congr eA]
    exact card_hyp_above (LinearMap.range ((T : W →ₗ[ZMod 2] W) - 1))
  have eB : {P : Submodule (ZMod 2) W //
        Module.finrank (ZMod 2) P = 1 ∧
          P.map (T : W →ₗ[ZMod 2] W) = P}
      ≃ {L : Submodule (ZMod 2) W //
        L ≤ LinearMap.ker ((T : W →ₗ[ZMod 2] W) - 1) ∧
          Module.finrank (ZMod 2) L = 1} :=
    Equiv.subtypeEquivRight fun P =>
      ⟨fun ⟨h1, h2⟩ => ⟨(line_invariant_iff_le_ker T P h1).mp h2, h1⟩,
       fun ⟨h1, h2⟩ => ⟨h2, (line_invariant_iff_le_ker T P h2).mpr h1⟩⟩
  have hB : Nat.card {P : Submodule (ZMod 2) W //
        Module.finrank (ZMod 2) P = 1 ∧
          P.map (T : W →ₗ[ZMod 2] W) = P}
      = 2 ^ (Module.finrank (ZMod 2) ↥(LinearMap.ker ((T : W →ₗ[ZMod 2] W) - 1))) - 1 := by
    rw [Nat.card_congr eB]
    rw [Nat.card_congr
      (submoduleLeOneEquivSubtype (LinearMap.ker ((T : W →ₗ[ZMod 2] W) - 1)))]
    rw [← Nat.card_congr
      (Projectivization.equivSubmodule (ZMod 2) ↥(LinearMap.ker ((T : W →ₗ[ZMod 2] W) - 1)))]
    have hcard : Nat.card (Projectivization (ZMod 2)
          ↥(LinearMap.ker ((T : W →ₗ[ZMod 2] W) - 1)))
        = Nat.card ↥(LinearMap.ker ((T : W →ₗ[ZMod 2] W) - 1)) - 1 := by
      have h := Projectivization.card'' (ZMod 2) ↥(LinearMap.ker ((T : W →ₗ[ZMod 2] W) - 1))
      rw [Nat.card_zmod] at h
      simpa using h
    rw [hcard]
    congr 1
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := ↥(LinearMap.ker ((T : W →ₗ[ZMod 2] W) - 1))), Nat.card_zmod]
  have hrn := LinearMap.finrank_range_add_finrank_ker ((T : W →ₗ[ZMod 2] W) - 1)
  have hexp : Module.finrank (ZMod 2) W -
        Module.finrank (ZMod 2) ↥(LinearMap.range ((T : W →ₗ[ZMod 2] W) - 1))
      = Module.finrank (ZMod 2) ↥(LinearMap.ker ((T : W →ₗ[ZMod 2] W) - 1)) := by
    omega
  rw [hA, hB, hexp]

end Work.Hering.Wagner
