import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.LinearAlgebra.Submodule

open Module

/-- **Additivity of the rank of a sum of linear maps.**
For linear maps `f g : W →ₗ[K] V` between finite-dimensional spaces over a field, the rank of
`f + g` equals the sum of the ranks of `f` and `g` if and only if the ranges intersect trivially,
they span the range of the sum, and the kernels span the whole space. -/
theorem finrank_range_add_iff {K W V : Type*} [Field K] [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f g : W →ₗ[K] V) :
    Module.finrank K (LinearMap.range (f + g)) =
      Module.finrank K (LinearMap.range f) + Module.finrank K (LinearMap.range g) ↔
      LinearMap.range f ⊓ LinearMap.range g = ⊥ ∧
      LinearMap.range f ⊔ LinearMap.range g = LinearMap.range (f + g) ∧
      LinearMap.ker f ⊔ LinearMap.ker g = ⊤ ∧
      LinearMap.ker (f + g) = LinearMap.ker f ⊓ LinearMap.ker g := by
  constructor
  · intro h
    have hle : LinearMap.range (f + g) ≤ LinearMap.range f ⊔ LinearMap.range g := by
      rintro y ⟨w, rfl⟩
      rw [LinearMap.add_apply]
      exact Submodule.add_mem _ (Submodule.mem_sup_left (LinearMap.mem_range_self f w))
        (Submodule.mem_sup_right (LinearMap.mem_range_self g w))
    have hfin_sup_le : Module.finrank K ↥(LinearMap.range f ⊔ LinearMap.range g) ≤
        Module.finrank K ↥(LinearMap.range (f + g)) := by
      rw [h]
      have := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range f) (LinearMap.range g)
      omega
    have heq : Module.finrank K ↥(LinearMap.range (f + g)) =
        Module.finrank K ↥(LinearMap.range f ⊔ LinearMap.range g) :=
      le_antisymm (Submodule.finrank_mono hle) hfin_sup_le
    have hsup : LinearMap.range f ⊔ LinearMap.range g = LinearMap.range (f + g) :=
      (Submodule.eq_of_le_of_finrank_eq hle heq).symm
    have hinf : LinearMap.range f ⊓ LinearMap.range g = ⊥ := by
      have hz : Module.finrank K ↥(LinearMap.range f ⊓ LinearMap.range g) = 0 := by
        have hdim := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range f) (LinearMap.range g)
        rw [← heq, h] at hdim
        omega
      exact (Submodule.finrank_eq_zero).mp hz
    have hkerfg : LinearMap.ker (f + g) = LinearMap.ker f ⊓ LinearMap.ker g := by
      ext w
      rw [LinearMap.mem_ker, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker,
        LinearMap.add_apply]
      constructor
      · intro hw
        have hfw : f w = g (-w) := by
          rw [map_neg, eq_comm, neg_eq_iff_add_eq_zero, add_comm]
          exact hw
        have hmem : f w ∈ LinearMap.range f ⊓ LinearMap.range g := by
          refine ⟨LinearMap.mem_range_self f w, ?_⟩
          rw [hfw]
          exact LinearMap.mem_range_self g (-w)
        rw [hinf, Submodule.mem_bot] at hmem
        constructor
        · exact hmem
        · rw [hmem, zero_add] at hw; exact hw
      · rintro ⟨hf, hg⟩
        rw [hf, hg, add_zero]
    have hrn := LinearMap.finrank_range_add_finrank_ker (f + g)
    rw [hkerfg] at hrn
    have hf := LinearMap.finrank_range_add_finrank_ker f
    have hg := LinearMap.finrank_range_add_finrank_ker g
    have hsupfin : Module.finrank K ↥(LinearMap.ker f ⊔ LinearMap.ker g) = Module.finrank K W := by
      have h2 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker f) (LinearMap.ker g)
      omega
    exact ⟨hinf, hsup, Submodule.eq_top_of_finrank_eq hsupfin, hkerfg⟩
  · rintro ⟨hinf, hsup, hker, hkerfg⟩
    rw [← hsup]
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range f) (LinearMap.range g)
    rw [hinf, finrank_bot, add_zero] at hdim
    omega

/-- **`lem:switching roles between derivatives lin-alg part` of arXiv:2209.04243 (Appendix).**
Let `V₁ ≤ V₂ ≤ V`, `W₂ ≤ W₁ ≤ W`, `X : W → V` with `ker X = W₁` and `range X = V₁`, and
`Y : W → V` with `X ≤ Y` (rank order), such that `V₂/V₁ ≤ range(Y(W₁,V/V₁))` and
`(Y(W₁,V/V₁))⁻¹(V₂/V₁) ≤ W₂`.
Then `V₃ = range(Y-X) ⊓ V₂` and `W₃ = ker(Y-X) ⊔ W₂` satisfy
`V₃ ⊔ V₁ = V₂`, `V₃ ⊓ V₁ = ⊥`, `W₃ ⊔ W₁ = ⊤`, `W₃ ⊓ W₁ = W₂`, `V₃ ≤ range Y`,
`Y⁻¹(V₃) ≤ W₃` and `X(W₃,V/V₃) ≤ Y(W₃,V/V₃)` (rank order on `↥W₃ → V/V₃`). -/
theorem exists_complement_pair_of_le_rank {K : Type*} [Field K] {V W : Type*} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (X Y : W →ₗ[K] V) (V₁ V₂ : Submodule K V) (W₁ W₂ : Submodule K W)
    (hXker : LinearMap.ker X = W₁) (hXrange : LinearMap.range X = V₁)
    (hV₁V₂ : V₁ ≤ V₂) (hW₂W₁ : W₂ ≤ W₁)
    (hXY : Module.finrank K (LinearMap.range Y) =
      Module.finrank K (LinearMap.range X) + Module.finrank K (LinearMap.range (Y - X)))
    (hV : Submodule.map (Submodule.mkQ V₁) V₂ ≤
      LinearMap.range ((Submodule.mkQ V₁).comp (Y.comp W₁.subtype)))
    (hW : Submodule.comap ((Submodule.mkQ V₁).comp (Y.comp W₁.subtype))
      (Submodule.map (Submodule.mkQ V₁) V₂) ≤ Submodule.comap W₁.subtype W₂) :
    let V₃ : Submodule K V := LinearMap.range (Y - X) ⊓ V₂
    let W₃ : Submodule K W := LinearMap.ker (Y - X) ⊔ W₂
    V₃ ⊔ V₁ = V₂ ∧ V₃ ⊓ V₁ = ⊥ ∧ W₃ ⊔ W₁ = ⊤ ∧ W₃ ⊓ W₁ = W₂ ∧
      V₃ ≤ LinearMap.range Y ∧ Submodule.comap Y V₃ ≤ W₃ ∧
      (Module.finrank K (LinearMap.range ((Submodule.mkQ V₃).comp (Y.comp W₃.subtype))) =
        Module.finrank K (LinearMap.range ((Submodule.mkQ V₃).comp (X.comp W₃.subtype))) +
        Module.finrank K (LinearMap.range
          (((Submodule.mkQ V₃).comp (Y.comp W₃.subtype)) -
            ((Submodule.mkQ V₃).comp (X.comp W₃.subtype))))) := by
  classical
  set Z : W →ₗ[K] V := Y - X with hZdef
  have hXZY : X + Z = Y := by
    rw [hZdef]; ext w; simp only [LinearMap.add_apply, LinearMap.sub_apply]; abel
  have hXY' : Module.finrank K (LinearMap.range (X + Z)) =
      Module.finrank K (LinearMap.range X) + Module.finrank K (LinearMap.range Z) := by
    rw [hXZY, hZdef]
    exact hXY
  obtain ⟨hinf, hsup, hker, hkerYZ⟩ := (finrank_range_add_iff X Z).mp hXY'
  rw [hXZY] at hsup hkerYZ
  have hZle : LinearMap.range Z ≤ LinearMap.range Y := by
    rw [← hsup]; exact le_sup_right
  have hkerY : LinearMap.ker Y = LinearMap.ker X ⊓ LinearMap.ker Z := hkerYZ
  dsimp only
  set V₃ : Submodule K V := LinearMap.range Z ⊓ V₂ with hV₃def
  set W₃ : Submodule K W := LinearMap.ker Z ⊔ W₂ with hW₃def
  have hmemW2 : ∀ {a : W}, a ∈ W₁ → Y a ∈ V₂ → a ∈ W₂ := by
    intro a ha hYa
    have hx : (⟨a, ha⟩ : ↥W₁) ∈ Submodule.comap
        ((Submodule.mkQ V₁).comp (Y.comp W₁.subtype))
        (Submodule.map (Submodule.mkQ V₁) V₂) := by
      rw [Submodule.mem_comap]
      exact Submodule.mem_map.mpr ⟨Y a, hYa, rfl⟩
    have h2 := Submodule.mem_comap.mp (hW hx)
    simpa using h2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- V₃ ⊔ V₁ = V₂
    rw [hV₃def]
    refine le_antisymm (sup_le inf_le_right hV₁V₂) ?_
    intro v hv
    have hvq : Submodule.mkQ V₁ v ∈ Submodule.map (Submodule.mkQ V₁) V₂ :=
      Submodule.mem_map.mpr ⟨v, hv, rfl⟩
    have hmem := hV hvq
    rw [LinearMap.mem_range] at hmem
    obtain ⟨x, hx⟩ := hmem
    have hx' : Submodule.mkQ V₁ (Y (x : W)) = Submodule.mkQ V₁ v := hx
    have hdv : Y (x : W) - v ∈ V₁ := by
      refine (Submodule.Quotient.eq V₁).mp ?_
      simpa only [Submodule.mkQ_apply] using hx'
    have hXx : X (x : W) = 0 := by
      have : (x : W) ∈ LinearMap.ker X := by rw [hXker]; exact x.2
      exact LinearMap.mem_ker.mp this
    have hZx : Z (x : W) = Y (x : W) := by
      simp only [hZdef, LinearMap.sub_apply, hXx, sub_zero]
    have hYxV2 : Y (x : W) ∈ V₂ := by
      have h1 : Y (x : W) - v ∈ V₂ := hV₁V₂ hdv
      have h2 : Y (x : W) = (Y (x : W) - v) + v := by abel
      rw [h2]; exact V₂.add_mem h1 hv
    refine Submodule.mem_sup.mpr ⟨Z (x : W), ?_, v - Y (x : W), ?_, ?_⟩
    · exact ⟨LinearMap.mem_range_self Z (x : W), by rw [hZx]; exact hYxV2⟩
    · simpa only [neg_sub] using V₁.neg_mem hdv
    · rw [hZx]; abel
  · -- V₃ ⊓ V₁ = ⊥
    rw [hV₃def, inf_assoc, inf_eq_right.mpr hV₁V₂, ← hXrange, inf_comm]
    exact hinf
  · -- W₃ ⊔ W₁ = ⊤
    rw [hW₃def, sup_assoc, sup_eq_right.mpr hW₂W₁, ← hXker, sup_comm]
    exact hker
  · -- W₃ ⊓ W₁ = W₂
    rw [hW₃def]
    refine le_antisymm ?_ (le_inf le_sup_right hW₂W₁)
    intro x hx
    rw [Submodule.mem_inf] at hx
    obtain ⟨hxsup, hxW1⟩ := hx
    obtain ⟨a, haKZ, b, hbW2, hab⟩ := Submodule.mem_sup.mp hxsup
    have haW1 : a ∈ W₁ := by
      have : a = x - b := by rw [← hab]; abel
      rw [this]
      exact W₁.sub_mem hxW1 (hW₂W₁ hbW2)
    have hXa : X a = 0 := by
      have : a ∈ LinearMap.ker X := by rw [hXker]; exact haW1
      exact LinearMap.mem_ker.mp this
    have hYa : Y a = 0 := by
      rw [← hXZY, LinearMap.add_apply, hXa, LinearMap.mem_ker.mp haKZ, add_zero]
    have haW2 : a ∈ W₂ := hmemW2 haW1 (by rw [hYa]; exact V₂.zero_mem)
    rw [← hab]
    exact W₂.add_mem haW2 hbW2
  · -- V₃ ≤ range Y
    rw [hV₃def]; exact le_trans inf_le_left hZle
  · -- comap Y V₃ ≤ W₃
    intro w hw
    rw [Submodule.mem_comap] at hw
    rw [hV₃def, Submodule.mem_inf] at hw
    have hYwZ : Y w ∈ LinearMap.range Z := hw.1
    obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hYwZ
    have hu_top : u ∈ LinearMap.ker X ⊔ LinearMap.ker Z := by
      rw [hker]; exact Submodule.mem_top
    obtain ⟨a, haKX, b, hbKZ, hab⟩ := Submodule.mem_sup.mp hu_top
    have haW1 : a ∈ W₁ := by rw [← hXker]; exact haKX
    have hYa : Y a = Y w := by
      have hZa : Z a = Y a := by
        have hXa : X a = 0 := LinearMap.mem_ker.mp haKX
        simp only [hZdef, LinearMap.sub_apply, hXa, sub_zero]
      have hZu : Z u = Z a := by
        rw [← hab, map_add, LinearMap.mem_ker.mp hbKZ, add_zero]
      rw [← hu, hZu, hZa]
    have haW2 : a ∈ W₂ := hmemW2 haW1 (by rw [hYa]; exact hw.2)
    have hwma : w - a ∈ LinearMap.ker Y := by
      rw [LinearMap.mem_ker, map_sub, hYa, sub_self]
    have hwmaZ : w - a ∈ LinearMap.ker Z := by
      rw [hkerY] at hwma
      exact hwma.2
    rw [hW₃def]
    exact Submodule.mem_sup.mpr ⟨w - a, hwmaZ, a, haW2, by abel⟩
  · -- the rank condition
    set f : ↥W₃ →ₗ[K] (V ⧸ V₃) := (Submodule.mkQ V₃).comp (X.comp W₃.subtype) with hfdef
    set g : ↥W₃ →ₗ[K] (V ⧸ V₃) := (Submodule.mkQ V₃).comp (Z.comp W₃.subtype) with hgdef
    have hfg : f + g = (Submodule.mkQ V₃).comp (Y.comp W₃.subtype) := by
      ext w
      show f w + g w = Submodule.mkQ V₃ (Y (W₃.subtype w))
      rw [hfdef, hgdef]
      simp only [LinearMap.comp_apply]
      rw [← map_add, ← hXZY, LinearMap.add_apply]
    have hrf : LinearMap.range f = Submodule.map (Submodule.mkQ V₃) (Submodule.map X W₃) := by
      rw [hfdef, LinearMap.range_comp, LinearMap.range_comp, Submodule.range_subtype]
    have hrg : LinearMap.range g = Submodule.map (Submodule.mkQ V₃) (Submodule.map Z W₃) := by
      rw [hgdef, LinearMap.range_comp, LinearMap.range_comp, Submodule.range_subtype]
    have hrfg : LinearMap.range (f + g)
        = Submodule.map (Submodule.mkQ V₃) (Submodule.map Y W₃) := by
      rw [hfg, LinearMap.range_comp, LinearMap.range_comp, Submodule.range_subtype]
    have hmapXZ : Submodule.map X W₃ ⊔ Submodule.map Z W₃ = Submodule.map Y W₃ := by
      refine le_antisymm ?_ ?_
      · refine sup_le ?_ ?_
        · rintro y ⟨w, hw, rfl⟩
          rw [hW₃def] at hw
          obtain ⟨p, hpKZ, q, hqW2, hpq⟩ := Submodule.mem_sup.mp hw
          have hXq : X q = 0 := by
            have : q ∈ LinearMap.ker X := by rw [hXker]; exact hW₂W₁ hqW2
            exact LinearMap.mem_ker.mp this
          have hp_eq : X p = Y p := by
            rw [← hXZY, LinearMap.add_apply, LinearMap.mem_ker.mp hpKZ, add_zero]
          refine Submodule.mem_map.mpr ⟨p, ?_, ?_⟩
          · rw [hW₃def]; exact Submodule.mem_sup_left hpKZ
          · rw [← hpq, map_add, hXq, add_zero, hp_eq]
        · rintro y ⟨w, hw, rfl⟩
          rw [hW₃def] at hw
          obtain ⟨p, hpKZ, q, hqW2, hpq⟩ := Submodule.mem_sup.mp hw
          have hXq : X q = 0 := by
            have : q ∈ LinearMap.ker X := by rw [hXker]; exact hW₂W₁ hqW2
            exact LinearMap.mem_ker.mp this
          have hq_eq : Z q = Y q := by
            rw [← hXZY, LinearMap.add_apply, hXq, zero_add]
          refine Submodule.mem_map.mpr ⟨q, ?_, ?_⟩
          · rw [hW₃def]; exact Submodule.mem_sup_right hqW2
          · rw [← hpq, map_add, LinearMap.mem_ker.mp hpKZ, zero_add, hq_eq]
      · rintro y ⟨w, hw, rfl⟩
        have : Y w = X w + Z w := by rw [← hXZY, LinearMap.add_apply]
        rw [this]
        exact Submodule.add_mem _
          (Submodule.mem_sup_left (Submodule.mem_map.mpr ⟨w, hw, rfl⟩))
          (Submodule.mem_sup_right (Submodule.mem_map.mpr ⟨w, hw, rfl⟩))
    have hinf_fg : LinearMap.range f ⊓ LinearMap.range g = ⊥ := by
      rw [hrf, hrg, eq_bot_iff]
      intro y hy
      rw [Submodule.mem_inf] at hy
      obtain ⟨hyA, hyB⟩ := hy
      rw [Submodule.mem_map] at hyA hyB
      obtain ⟨x, hx, rfl⟩ := hyA
      obtain ⟨z, hz, hzy⟩ := hyB
      rw [Submodule.mem_bot]
      have hxzV3 : x - z ∈ V₃ := by
        refine (Submodule.Quotient.eq V₃).mp ?_
        simpa only [Submodule.mkQ_apply] using hzy.symm
      have hxzRZ : x - z ∈ LinearMap.range Z := by
        rw [hV₃def] at hxzV3
        exact hxzV3.1
      have hzRZ : z ∈ LinearMap.range Z := by
        have h := Submodule.map_mono (le_top : W₃ ≤ ⊤) hz
        rwa [Submodule.map_top] at h
      have hxV2 : x ∈ V₂ := by
        have hxRX : x ∈ LinearMap.range X := by
          have h := Submodule.map_mono (le_top : W₃ ≤ ⊤) hx
          rwa [Submodule.map_top] at h
        exact hV₁V₂ (by rw [← hXrange]; exact hxRX)
      have hxRZ : x ∈ LinearMap.range Z := by
        have hxx : x = (x - z) + z := by abel
        rw [hxx]
        exact (LinearMap.range Z).add_mem hxzRZ hzRZ
      have hxV3 : x ∈ V₃ := by
        rw [hV₃def]; exact ⟨hxRZ, hxV2⟩
      simpa only [Submodule.mkQ_apply] using (Submodule.Quotient.mk_eq_zero V₃).mpr hxV3
    have hsup_fg : LinearMap.range f ⊔ LinearMap.range g = LinearMap.range (f + g) := by
      rw [hrf, hrg, hrfg, ← Submodule.map_sup, hmapXZ]
    have hYeq : (Submodule.mkQ V₃).comp (Y.comp W₃.subtype) = f + g := hfg.symm
    rw [hYeq, show (f + g) - f = g from by abel]
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range f) (LinearMap.range g)
    rw [hsup_fg, hinf_fg, finrank_bot, add_zero] at hdim
    exact hdim

end Commons.LinearAlgebra.Submodule