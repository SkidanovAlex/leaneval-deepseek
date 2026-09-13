import Mathlib
import Submission.Commons.LinearAlgebra.finrank_comap_eq
import Submission.Commons.LinearAlgebra.finrank_map_eq
import Submission.Commons.LinearAlgebra.Matrix.rank_sandwich_poset

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Commons.LinearAlgebra.Submodule

namespace SwappingPlaces

variable {K : Type*} [Field K]

/-- Auxiliary dimension estimate. -/
theorem finrank_range_comp_mkQ_subtype_add_ge {V W : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (Z : W →ₗ[K] V) (V₁ : Submodule K V) (T : Submodule K W) :
    Module.finrank K (LinearMap.range ((Submodule.mkQ V₁).comp (Z.comp T.subtype))) +
      Module.finrank K V₁ + Module.finrank K (W ⧸ T) ≥ Module.finrank K (LinearMap.range Z) := by
  classical
  set g : T →ₗ[K] (V ⧸ V₁) := (Submodule.mkQ V₁).comp (Z.comp T.subtype) with hg
  have hker : LinearMap.ker g = Submodule.comap T.subtype (Submodule.comap Z V₁) := by
    rw [hg]
    ext x
    simp [LinearMap.mem_ker, Submodule.mem_comap]
  have hkerfin : Module.finrank K ↥(LinearMap.ker g) =
      Module.finrank K ↥(T ⊓ Submodule.comap Z V₁) := by
    rw [hker, Commons.LinearAlgebra.finrank_comap_eq T.subtype (Submodule.comap Z V₁),
      Submodule.ker_subtype, Submodule.range_subtype, finrank_bot, zero_add, inf_comm]
  have hrn : Module.finrank K (LinearMap.range g) +
      Module.finrank K ↥(T ⊓ Submodule.comap Z V₁) = Module.finrank K T := by
    have h := LinearMap.finrank_range_add_finrank_ker g
    rwa [hkerfin] at h
  have hs_le : Module.finrank K ↥(T ⊓ Submodule.comap Z V₁) ≤
      Module.finrank K ↥(Submodule.comap Z V₁) := Submodule.finrank_mono inf_le_right
  have hcomap : Module.finrank K ↥(Submodule.comap Z V₁) =
      Module.finrank K (LinearMap.ker Z) + Module.finrank K ↥(V₁ ⊓ LinearMap.range Z) :=
    Commons.LinearAlgebra.finrank_comap_eq Z V₁
  have hkerZ : Module.finrank K (LinearMap.ker Z) =
      Module.finrank K W - Module.finrank K (LinearMap.range Z) := by
    have h := LinearMap.finrank_range_add_finrank_ker Z
    omega
  have hrankW : Module.finrank K (LinearMap.range Z) + Module.finrank K (LinearMap.ker Z) =
      Module.finrank K W := LinearMap.finrank_range_add_finrank_ker Z
  have ht_le : Module.finrank K ↥(V₁ ⊓ LinearMap.range Z) ≤ Module.finrank K V₁ :=
    Submodule.finrank_mono inf_le_left
  have hs_le_T : Module.finrank K ↥(T ⊓ Submodule.comap Z V₁) ≤ Module.finrank K T :=
    Submodule.finrank_mono inf_le_left
  have hq : Module.finrank K (W ⧸ T) = Module.finrank K W - Module.finrank K T :=
    Nat.eq_sub_of_add_eq (Submodule.finrank_quotient_add_finrank T)
  omega

/-- Auxiliary: equality in the dimension estimate forces `V₁ ≤ range Z` and `Z⁻¹V₁ ≤ T`. -/
theorem le_range_and_comap_le_of_finrank_range_comp_mkQ_subtype_add_eq {V W : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (Z : W →ₗ[K] V) (V₁ : Submodule K V) (T : Submodule K W)
    (h : Module.finrank K (LinearMap.range ((Submodule.mkQ V₁).comp (Z.comp T.subtype))) +
      Module.finrank K V₁ + Module.finrank K (W ⧸ T) = Module.finrank K (LinearMap.range Z)) :
    V₁ ≤ LinearMap.range Z ∧ Submodule.comap Z V₁ ≤ T := by
  classical
  set g : T →ₗ[K] (V ⧸ V₁) := (Submodule.mkQ V₁).comp (Z.comp T.subtype) with hg
  have hker : LinearMap.ker g = Submodule.comap T.subtype (Submodule.comap Z V₁) := by
    rw [hg]
    ext x
    simp [LinearMap.mem_ker, Submodule.mem_comap]
  have hkerfin : Module.finrank K ↥(LinearMap.ker g) =
      Module.finrank K ↥(T ⊓ Submodule.comap Z V₁) := by
    rw [hker, Commons.LinearAlgebra.finrank_comap_eq T.subtype (Submodule.comap Z V₁),
      Submodule.ker_subtype, Submodule.range_subtype, finrank_bot, zero_add, inf_comm]
  have hrn : Module.finrank K (LinearMap.range g) +
      Module.finrank K ↥(T ⊓ Submodule.comap Z V₁) = Module.finrank K T := by
    have h := LinearMap.finrank_range_add_finrank_ker g
    rwa [hkerfin] at h
  have hs_le : Module.finrank K ↥(T ⊓ Submodule.comap Z V₁) ≤
      Module.finrank K ↥(Submodule.comap Z V₁) := Submodule.finrank_mono inf_le_right
  have hcomap : Module.finrank K ↥(Submodule.comap Z V₁) =
      Module.finrank K (LinearMap.ker Z) + Module.finrank K ↥(V₁ ⊓ LinearMap.range Z) :=
    Commons.LinearAlgebra.finrank_comap_eq Z V₁
  have hkerZ : Module.finrank K (LinearMap.ker Z) =
      Module.finrank K W - Module.finrank K (LinearMap.range Z) := by
    have h := LinearMap.finrank_range_add_finrank_ker Z
    omega
  have hrankW : Module.finrank K (LinearMap.range Z) + Module.finrank K (LinearMap.ker Z) =
      Module.finrank K W := LinearMap.finrank_range_add_finrank_ker Z
  have ht_le : Module.finrank K ↥(V₁ ⊓ LinearMap.range Z) ≤ Module.finrank K V₁ :=
    Submodule.finrank_mono inf_le_left
  have hs_le_T : Module.finrank K ↥(T ⊓ Submodule.comap Z V₁) ≤ Module.finrank K T :=
    Submodule.finrank_mono inf_le_left
  have hq : Module.finrank K (W ⧸ T) = Module.finrank K W - Module.finrank K T :=
    Nat.eq_sub_of_add_eq (Submodule.finrank_quotient_add_finrank T)
  -- key arithmetic consequences
  have ht_eq : Module.finrank K ↥(V₁ ⊓ LinearMap.range Z) = Module.finrank K V₁ := by omega
  have hs_eq : Module.finrank K ↥(T ⊓ Submodule.comap Z V₁) =
      Module.finrank K ↥(Submodule.comap Z V₁) := by omega
  constructor
  · have hinf : V₁ ⊓ LinearMap.range Z = V₁ :=
      Submodule.eq_of_le_of_finrank_eq inf_le_left ht_eq
    exact inf_eq_left.mp hinf
  · have hinf : T ⊓ Submodule.comap Z V₁ = Submodule.comap Z V₁ :=
      Submodule.eq_of_le_of_finrank_eq inf_le_right hs_eq
    exact inf_eq_right.mp hinf

/-- Auxiliary: the forward dimension formula. -/
theorem finrank_range_comp_mkQ_subtype_add_eq_of_le {V W : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (Z : W →ₗ[K] V) (V₁ : Submodule K V) (T : Submodule K W)
    (hV : V₁ ≤ LinearMap.range Z) (hW : Submodule.comap Z V₁ ≤ T) :
    Module.finrank K (LinearMap.range ((Submodule.mkQ V₁).comp (Z.comp T.subtype))) +
      Module.finrank K V₁ + Module.finrank K (W ⧸ T) = Module.finrank K (LinearMap.range Z) := by
  classical
  set g : T →ₗ[K] (V ⧸ V₁) := (Submodule.mkQ V₁).comp (Z.comp T.subtype) with hg
  have hker : LinearMap.ker g = Submodule.comap T.subtype (Submodule.comap Z V₁) := by
    rw [hg]
    ext x
    simp [LinearMap.mem_ker, Submodule.mem_comap]
  have hkerfin : Module.finrank K ↥(LinearMap.ker g) =
      Module.finrank K ↥(T ⊓ Submodule.comap Z V₁) := by
    rw [hker, Commons.LinearAlgebra.finrank_comap_eq T.subtype (Submodule.comap Z V₁),
      Submodule.ker_subtype, Submodule.range_subtype, finrank_bot, zero_add, inf_comm]
  have hrn : Module.finrank K (LinearMap.range g) +
      Module.finrank K ↥(T ⊓ Submodule.comap Z V₁) = Module.finrank K T := by
    have h := LinearMap.finrank_range_add_finrank_ker g
    rwa [hkerfin] at h
  have hs_eq : Module.finrank K ↥(T ⊓ Submodule.comap Z V₁) =
      Module.finrank K ↥(Submodule.comap Z V₁) := by
    rw [inf_eq_right.mpr hW]
  have hcomap : Module.finrank K ↥(Submodule.comap Z V₁) =
      Module.finrank K (LinearMap.ker Z) + Module.finrank K ↥(V₁ ⊓ LinearMap.range Z) :=
    Commons.LinearAlgebra.finrank_comap_eq Z V₁
  have ht_eq : Module.finrank K ↥(V₁ ⊓ LinearMap.range Z) = Module.finrank K V₁ := by
    rw [inf_eq_left.mpr hV]
  have hrankW : Module.finrank K (LinearMap.range Z) + Module.finrank K (LinearMap.ker Z) =
      Module.finrank K W := LinearMap.finrank_range_add_finrank_ker Z
  have hs_le_T : Module.finrank K ↥(T ⊓ Submodule.comap Z V₁) ≤ Module.finrank K T :=
    Submodule.finrank_mono inf_le_left
  have ht_le_r : Module.finrank K ↥(V₁ ⊓ LinearMap.range Z) ≤
      Module.finrank K (LinearMap.range Z) := Submodule.finrank_mono inf_le_right
  have hk_le : Module.finrank K T ≤ Module.finrank K W := by
    simpa using Submodule.finrank_mono (show T ≤ (⊤ : Submodule K W) from le_top)
  have hq : Module.finrank K (W ⧸ T) = Module.finrank K W - Module.finrank K T :=
    Nat.eq_sub_of_add_eq (Submodule.finrank_quotient_add_finrank T)
  omega
/-- Membership in the kernel of the quotient map. -/
lemma mkQ_eq_zero_iff {V : Type*} [AddCommGroup V] [Module K V]
    (p : Submodule K V) (x : V) : p.mkQ x = 0 ↔ x ∈ p := by
  rw [← LinearMap.mem_ker, Submodule.ker_mkQ]

/-- Membership of a quotient in the image of a submodule under the quotient map. -/
lemma mkQ_mem_map_mkQ_iff {V : Type*} [AddCommGroup V] [Module K V]
    (p A : Submodule K V) (x : V) :
    p.mkQ x ∈ Submodule.map p.mkQ A ↔ x ∈ A ⊔ p := by
  rw [← Submodule.mem_comap, Submodule.comap_map_mkQ, sup_comm]

end SwappingPlaces

open SwappingPlaces

/-- **`Lem: swapping places 2` of arXiv:2209.04243 (Appendix).**
Let `V₁ ≤ V₂ ≤ V`, `W₂ ≤ W₁ ≤ W`, and `X : W → V` with `ker X = W₁`, `range X = V₁`.
Let `V₃ ≤ V₂`, `W₂ ≤ W₃` with `V₃ ⊔ V₁ = V₂`, `V₃ ⊓ V₁ = ⊥`, `W₃ ⊔ W₁ = ⊤`,
`W₃ ⊓ W₁ = W₂`, and let `Y : W → V` with `V₃ ≤ range Y`, `Y⁻¹(V₃) ≤ W₃` and
`X(W₃,V/V₃) ≤ Y(W₃,V/V₃)` (rank order on `↥W₃ → V/V₃`).
Then `X ≤ Y`, `V₂/V₁ ≤ range(Y(W₁,V/V₁))`, `(Y(W₁,V/V₁))⁻¹(V₂/V₁) ≤ W₂`,
`range(Y-X) ⊓ V₂ = V₃` and `ker(Y-X) ⊔ W₂ = W₃`. -/
theorem swapping_places {K : Type*} [Field K] {V W : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (X Y : W →ₗ[K] V) (V₁ V₂ V₃ : Submodule K V) (W₁ W₂ W₃ : Submodule K W)
    (hXker : LinearMap.ker X = W₁) (hXrange : LinearMap.range X = V₁)
    (hVsup : V₃ ⊔ V₁ = V₂) (hVinf : V₃ ⊓ V₁ = ⊥)
    (hWsup : W₃ ⊔ W₁ = ⊤) (hWinf : W₃ ⊓ W₁ = W₂)
    (hYV : V₃ ≤ LinearMap.range Y) (hYW : Submodule.comap Y V₃ ≤ W₃)
    (hXY : Module.finrank K (LinearMap.range ((Submodule.mkQ V₃).comp (Y.comp W₃.subtype))) =
      Module.finrank K (LinearMap.range ((Submodule.mkQ V₃).comp (X.comp W₃.subtype))) +
      Module.finrank K (LinearMap.range
        (((Submodule.mkQ V₃).comp (Y.comp W₃.subtype)) -
          ((Submodule.mkQ V₃).comp (X.comp W₃.subtype))))) :
    (Module.finrank K (LinearMap.range Y) =
      Module.finrank K (LinearMap.range X) + Module.finrank K (LinearMap.range (Y - X))) ∧
    Submodule.map (Submodule.mkQ V₁) V₂ ≤
      LinearMap.range ((Submodule.mkQ V₁).comp (Y.comp W₁.subtype)) ∧
    Submodule.comap ((Submodule.mkQ V₁).comp (Y.comp W₁.subtype))
      (Submodule.map (Submodule.mkQ V₁) V₂) ≤ Submodule.comap W₁.subtype W₂ ∧
    LinearMap.range (Y - X) ⊓ V₂ = V₃ ∧
    LinearMap.ker (Y - X) ⊔ W₂ = W₃ := by
  classical
  have hVinf' : V₁ ⊓ V₃ = ⊥ := by rw [inf_comm, hVinf]
  have hVsup' : V₁ ⊔ V₃ = V₂ := by rw [sup_comm, hVsup]
  have hWinf' : W₁ ⊓ W₃ = W₂ := by rw [inf_comm, hWinf]
  have hV1_le_V2 : V₁ ≤ V₂ := by rw [← hVsup]; exact le_sup_right
  have hV3_le_V2 : V₃ ≤ V₂ := by rw [← hVsup]; exact le_sup_left
  have hXfin : Module.finrank K (LinearMap.range X) = Module.finrank K V₁ := by rw [hXrange]
  have hmapX : Submodule.map X W₃ = V₁ := by
    have htop : W₃ ⊔ LinearMap.ker X = ⊤ := by rw [hXker, hWsup]
    have hkerbot : Submodule.map X (LinearMap.ker X) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      rintro y ⟨x, hx, rfl⟩
      simpa [LinearMap.mem_ker] using hx
    have h := congrArg (fun s : Submodule K W => Submodule.map X s) htop
    rw [Submodule.map_sup, hkerbot, sup_bot_eq, Submodule.map_top, hXrange] at h
    exact h
  set A : W₃ →ₗ[K] V ⧸ V₃ := (Submodule.mkQ V₃).comp (X.comp W₃.subtype) with hA
  set B : W₃ →ₗ[K] V ⧸ V₃ := (Submodule.mkQ V₃).comp (Y.comp W₃.subtype) with hB
  have hXY' : Module.finrank K (LinearMap.range B) =
      Module.finrank K (LinearMap.range A) + Module.finrank K (LinearMap.range (B - A)) := by
    simpa [hA, hB] using hXY
  have hA_range : LinearMap.range A = Submodule.map (Submodule.mkQ V₃) V₁ := by
    rw [hA, LinearMap.range_comp, LinearMap.range_comp, Submodule.range_subtype, hmapX]
  have hAfin : Module.finrank K (LinearMap.range A) = Module.finrank K V₁ := by
    rw [hA_range, Commons.LinearAlgebra.finrank_map_eq, Submodule.ker_mkQ, hVinf', finrank_bot]
    omega
  have hBfin : Module.finrank K (LinearMap.range B) + Module.finrank K V₃ +
      Module.finrank K (W ⧸ W₃) = Module.finrank K (LinearMap.range Y) := by
    rw [hB]
    exact finrank_range_comp_mkQ_subtype_add_eq_of_le Y V₃ W₃ hYV hYW
  have hBAfin : Module.finrank K (LinearMap.range (B - A)) + Module.finrank K V₃ +
      Module.finrank K (W ⧸ W₃) = Module.finrank K (LinearMap.range Y) - Module.finrank K V₁ := by
    omega
  have hsubBA : B - A = (Submodule.mkQ V₃).comp ((Y - X).comp W₃.subtype) := by
    rw [hA, hB]
    ext w
    simp [LinearMap.sub_apply, LinearMap.comp_apply]
  have hZfin : Module.finrank K (LinearMap.range ((Submodule.mkQ V₃).comp ((Y - X).comp W₃.subtype))) +
      Module.finrank K V₃ + Module.finrank K (W ⧸ W₃) =
      Module.finrank K (LinearMap.range Y) - Module.finrank K V₁ := by
    rw [← hsubBA]
    exact hBAfin
  -- upper bound for the rank of `Y - X`
  have hge := finrank_range_comp_mkQ_subtype_add_ge (Y - X) V₃ W₃
  have hZ_le : Module.finrank K (LinearMap.range (Y - X)) ≤
      Module.finrank K (LinearMap.range Y) - Module.finrank K V₁ := by
    omega
  -- lower bound
  have hgen : Module.finrank K (LinearMap.range Y) ≤ Module.finrank K (LinearMap.range X) +
      Module.finrank K (LinearMap.range (Y - X)) := by
    have hle : LinearMap.range Y ≤ LinearMap.range X ⊔ LinearMap.range (Y - X) := by
      rintro y ⟨w, rfl⟩
      have hw : Y w = X w + (Y - X) w := by rw [LinearMap.sub_apply]; abel
      exact Submodule.mem_sup.mpr ⟨X w, LinearMap.mem_range_self X w, (Y - X) w,
        LinearMap.mem_range_self (Y - X) w, hw.symm⟩
    calc Module.finrank K (LinearMap.range Y)
        ≤ Module.finrank K ↥(LinearMap.range X ⊔ LinearMap.range (Y - X)) :=
          Submodule.finrank_mono hle
      _ ≤ Module.finrank K ↥(LinearMap.range X) + Module.finrank K ↥(LinearMap.range (Y - X)) :=
          Submodule.finrank_add_le_finrank_add_finrank _ _
  have hZ_eq : Module.finrank K (LinearMap.range (Y - X)) =
      Module.finrank K (LinearMap.range Y) - Module.finrank K V₁ := by
    omega
  have hconcl1 : Module.finrank K (LinearMap.range Y) =
      Module.finrank K (LinearMap.range X) + Module.finrank K (LinearMap.range (Y - X)) := by
    omega
  -- the equality case gives the two key properties of `Y - X`
  have hZeq : Module.finrank K
        (LinearMap.range ((Submodule.mkQ V₃).comp ((Y - X).comp W₃.subtype))) +
      Module.finrank K V₃ + Module.finrank K (W ⧸ W₃) =
      Module.finrank K (LinearMap.range (Y - X)) := by
    omega
  obtain ⟨hV3_le_rangeZ, hcomapZ_le_W3⟩ :=
    le_range_and_comap_le_of_finrank_range_comp_mkQ_subtype_add_eq (Y - X) V₃ W₃ hZeq
  -- rank-poset consequences
  have hinfXY : LinearMap.range X ⊓ LinearMap.range (Y - X) = ⊥ :=
    (Commons.LinearAlgebra.range_inf_bot_and_map_ker_eq_range_of_finrank_range_add X (Y - X)
      (by rw [add_sub_cancel]; exact hconcl1)).1
  have hagree : ∀ w : W, Y w ∈ LinearMap.range X → X w = Y w := by
    intro w hw
    have hmem : (Y - X) w ∈ LinearMap.range X ⊓ LinearMap.range (Y - X) := by
      refine Submodule.mem_inf.mpr ⟨?_, LinearMap.mem_range_self (Y - X) w⟩
      obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hw
      refine ⟨u - w, ?_⟩
      rw [LinearMap.sub_apply, LinearMap.map_sub, hu]
    rw [hinfXY] at hmem
    have h0 : (Y - X) w = 0 := by simpa using hmem
    have h1 : Y w - X w = 0 := by simpa [LinearMap.sub_apply] using h0
    exact (sub_eq_zero.mp h1).symm
  have hkerY_le_W1 : LinearMap.ker Y ≤ W₁ := by
    intro w hw
    rw [← hXker, LinearMap.mem_ker]
    have hYw : Y w = 0 := LinearMap.mem_ker.mp hw
    have hmem : X w ∈ LinearMap.range X ⊓ LinearMap.range (Y - X) := by
      refine Submodule.mem_inf.mpr ⟨LinearMap.mem_range_self X w, ?_⟩
      refine ⟨-w, ?_⟩
      simp [LinearMap.sub_apply, hYw]
    rw [hinfXY] at hmem
    simpa using hmem
  have hkerY_le_comap : LinearMap.ker Y ≤ Submodule.comap Y V₃ := by
    intro w hw
    rw [Submodule.mem_comap, LinearMap.mem_ker.mp hw]
    exact V₃.zero_mem
  have hkerY_le_W2 : LinearMap.ker Y ≤ W₂ := by
    intro w hw
    rw [← hWinf, Submodule.mem_inf]
    exact ⟨hYW (hkerY_le_comap hw), hkerY_le_W1 hw⟩
  have hkerZ_le_W3 : LinearMap.ker (Y - X) ≤ W₃ :=
    le_trans (fun w hw => by
      rw [Submodule.mem_comap, LinearMap.mem_ker.mp hw]
      exact V₃.zero_mem) hcomapZ_le_W3
  have hinfAB : LinearMap.range A ⊓ LinearMap.range (B - A) = ⊥ :=
    (Commons.LinearAlgebra.range_inf_bot_and_map_ker_eq_range_of_finrank_range_add A (B - A)
      (by rw [add_sub_cancel]; exact hXY')).1
  refine ⟨hconcl1, ?_, ?_, ?_, ?_⟩
  · -- (ii)
    have hV3_le_sup : V₃ ≤ V₁ ⊔ Submodule.map Y W₁ := by
      intro v hv
      obtain ⟨w, hw⟩ := LinearMap.mem_range.mp (hYV hv)
      have hw3 : w ∈ W₃ := hYW (by rw [Submodule.mem_comap]; rw [hw]; exact hv)
      have hXw : X w = 0 := by
        have hAw0 : A ⟨w, hw3⟩ = 0 := by
          have hBw0 : B ⟨w, hw3⟩ = 0 := by
            rw [hB]
            simp only [LinearMap.comp_apply, Submodule.subtype_apply]
            rw [hw]
            exact (mkQ_eq_zero_iff V₃ v).mpr hv
          have hmem : A ⟨w, hw3⟩ ∈ LinearMap.range A ⊓ LinearMap.range (B - A) := by
            refine Submodule.mem_inf.mpr ⟨LinearMap.mem_range_self A _, ?_⟩
            refine ⟨-⟨w, hw3⟩, ?_⟩
            rw [map_neg, LinearMap.sub_apply, hBw0, zero_sub, neg_neg]
          rw [hinfAB] at hmem
          simpa using hmem
        have hXw3 : X w ∈ V₃ := by
          rw [hA] at hAw0
          simp only [LinearMap.comp_apply, Submodule.subtype_apply] at hAw0
          exact (mkQ_eq_zero_iff V₃ (X w)).mp hAw0
        have hmem : X w ∈ V₁ ⊓ V₃ :=
          Submodule.mem_inf.mpr ⟨by rw [← hXrange]; exact LinearMap.mem_range_self X w, hXw3⟩
        rw [hVinf'] at hmem
        simpa using hmem
      have hwW1 : w ∈ W₁ := by rw [← hXker, LinearMap.mem_ker]; exact hXw
      exact Submodule.mem_sup.mpr ⟨0, V₁.zero_mem, Y w, ⟨w, hwW1, rfl⟩, by rw [zero_add]; exact hw⟩
    have hV2_le : V₂ ≤ V₁ ⊔ Submodule.map Y W₁ := by
      rw [← hVsup]
      exact sup_le hV3_le_sup le_sup_left
    have hmapYW1 : Submodule.map Y W₁ = LinearMap.range (Y.comp W₁.subtype) := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
    have hmapmkQ : LinearMap.range ((Submodule.mkQ V₁).comp (Y.comp W₁.subtype)) =
        Submodule.map (Submodule.mkQ V₁) (Submodule.map Y W₁) := by
      rw [LinearMap.range_comp, LinearMap.range_comp, Submodule.range_subtype]
    calc Submodule.map (Submodule.mkQ V₁) V₂
        ≤ Submodule.map (Submodule.mkQ V₁) (V₁ ⊔ Submodule.map Y W₁) :=
          Submodule.map_mono hV2_le
      _ = Submodule.map (Submodule.mkQ V₁) V₁ ⊔
            Submodule.map (Submodule.mkQ V₁) (Submodule.map Y W₁) := by rw [Submodule.map_sup]
      _ = LinearMap.range ((Submodule.mkQ V₁).comp (Y.comp W₁.subtype)) := by
          rw [Submodule.mkQ_map_self, bot_sup_eq]
          exact hmapmkQ.symm
  · -- (iii)
    intro x hx
    rw [Submodule.mem_comap] at hx ⊢
    have hYx : Y (x : W) ∈ V₂ := by
      have h1 : Y (x : W) ∈ V₂ ⊔ V₁ := (mkQ_mem_map_mkQ_iff V₁ V₂ (Y (x : W))).mp hx
      rwa [sup_eq_left.mpr hV1_le_V2] at h1
    rw [← hVsup'] at hYx
    obtain ⟨v₁, hv₁, v₃, hv₃, hsum⟩ := Submodule.mem_sup.mp hYx
    obtain ⟨w₃, hw₃⟩ := LinearMap.mem_range.mp (hYV hv₃)
    have hw₃W3 : w₃ ∈ W₃ := hYW (by rw [Submodule.mem_comap]; rw [hw₃]; exact hv₃)
    have hY_xx : Y ((x : W) - w₃) = v₁ := by
      rw [LinearMap.map_sub, hw₃]
      rw [← hsum]
      abel
    have hdiff : (x : W) - w₃ ∈ LinearMap.ker (Y - X) := by
      rw [LinearMap.mem_ker]
      have h1 : X ((x : W) - w₃) = Y ((x : W) - w₃) :=
        hagree _ (by rw [hY_xx]; exact hXrange ▸ hv₁)
      rw [LinearMap.sub_apply, h1, sub_self]
    have hxW3 : (x : W) ∈ W₃ := by
      have hxeq : (x : W) = ((x : W) - w₃) + w₃ := by abel
      rw [hxeq]
      exact W₃.add_mem (hkerZ_le_W3 hdiff) hw₃W3
    rw [← hWinf', Submodule.mem_inf]
    exact ⟨x.2, hxW3⟩
  · -- (iv)
    have hle : V₃ ≤ LinearMap.range (Y - X) ⊓ V₂ := le_inf hV3_le_rangeZ hV3_le_V2
    have hT_inf : (LinearMap.range (Y - X) ⊓ V₂) ⊓ V₁ = ⊥ := by
      calc (LinearMap.range (Y - X) ⊓ V₂) ⊓ V₁
          = LinearMap.range (Y - X) ⊓ (V₂ ⊓ V₁) := inf_assoc _ _ _
        _ = LinearMap.range (Y - X) ⊓ V₁ := by rw [inf_eq_right.mpr hV1_le_V2]
        _ = LinearMap.range (Y - X) ⊓ LinearMap.range X := by rw [← hXrange]
        _ = ⊥ := by rw [inf_comm]; exact hinfXY
    have hfin : Module.finrank K ↥(LinearMap.range (Y - X) ⊓ V₂) ≤
        Module.finrank K V₃ := by
      have h2 : Module.finrank K ↥((LinearMap.range (Y - X) ⊓ V₂) ⊔ V₁) ≤
          Module.finrank K V₂ :=
        Submodule.finrank_mono (sup_le inf_le_right hV1_le_V2)
      have h3 : Module.finrank K V₂ = Module.finrank K V₃ + Module.finrank K V₁ := by
        have h := Submodule.finrank_sup_add_finrank_inf_eq V₃ V₁
        rw [hVsup, hVinf, finrank_bot, add_zero] at h
        omega
      have h4 : Module.finrank K ↥(LinearMap.range (Y - X) ⊓ V₂) =
          Module.finrank K ↥((LinearMap.range (Y - X) ⊓ V₂) ⊔ V₁) - Module.finrank K V₁ := by
        have h := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range (Y - X) ⊓ V₂) V₁
        rw [hT_inf, finrank_bot, add_zero] at h
        omega
      omega
    exact (Submodule.eq_of_le_of_finrank_le hle hfin).symm
  · -- (v)
    have hle : LinearMap.ker (Y - X) ⊔ W₂ ≤ W₃ :=
      sup_le hkerZ_le_W3 (by rw [← hWinf]; exact inf_le_left)
    have hker_inf : LinearMap.ker (Y - X) ⊓ W₂ = LinearMap.ker Y := by
      refine le_antisymm ?_ ?_
      · intro w hw
        rw [Submodule.mem_inf] at hw
        rw [LinearMap.mem_ker]
        have hXw : X w = 0 := by
          have h2 : w ∈ W₁ ⊓ W₃ := by rw [hWinf']; exact hw.2
          have h4 : w ∈ LinearMap.ker X := hXker.symm ▸ h2.1
          exact LinearMap.mem_ker.mp h4
        have hZw : (Y - X) w = 0 := LinearMap.mem_ker.mp hw.1
        have hYXY : Y w = (Y - X) w + X w := by rw [LinearMap.sub_apply]; abel
        rw [hYXY, hZw, hXw, zero_add]
      · intro w hw
        rw [Submodule.mem_inf]
        refine ⟨?_, hkerY_le_W2 hw⟩
        rw [LinearMap.mem_ker]
        have hXw : X w = 0 := by
          have h1 := hkerY_le_W1 hw
          rwa [← hXker, LinearMap.mem_ker] at h1
        rw [LinearMap.sub_apply, LinearMap.mem_ker.mp hw, hXw, sub_zero]
    have hkey : Module.finrank K ↥(LinearMap.ker (Y - X) ⊔ W₂) +
        Module.finrank K ↥(LinearMap.ker Y) =
        Module.finrank K ↥(LinearMap.ker (Y - X)) + Module.finrank K W₂ := by
      have h := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker (Y - X)) W₂
      rwa [hker_inf] at h
    have hZ_ker : Module.finrank K ↥(LinearMap.ker (Y - X)) =
        Module.finrank K W - Module.finrank K (LinearMap.range (Y - X)) := by
      have h := LinearMap.finrank_range_add_finrank_ker (Y - X)
      omega
    have hY_ker : Module.finrank K ↥(LinearMap.ker Y) =
        Module.finrank K W - Module.finrank K (LinearMap.range Y) := by
      have h := LinearMap.finrank_range_add_finrank_ker Y
      omega
    have hW3 : Module.finrank K W₃ + Module.finrank K W₁ =
        Module.finrank K W + Module.finrank K W₂ := by
      have h := Submodule.finrank_sup_add_finrank_inf_eq W₃ W₁
      rw [hWsup, hWinf, finrank_top] at h
      omega
    have hW1 : Module.finrank K W₁ = Module.finrank K W - Module.finrank K V₁ := by
      have h := LinearMap.finrank_range_add_finrank_ker X
      rw [hXrange, hXker] at h
      omega
    have hrankX : Module.finrank K (LinearMap.range X) + Module.finrank K (LinearMap.ker X) =
        Module.finrank K W := LinearMap.finrank_range_add_finrank_ker X
    have hrankY : Module.finrank K (LinearMap.range Y) + Module.finrank K (LinearMap.ker Y) =
        Module.finrank K W := LinearMap.finrank_range_add_finrank_ker Y
    have hrankZ : Module.finrank K (LinearMap.range (Y - X)) +
        Module.finrank K (LinearMap.ker (Y - X)) = Module.finrank K W :=
      LinearMap.finrank_range_add_finrank_ker (Y - X)
    have hsum_fin : Module.finrank K ↥(LinearMap.ker (Y - X) ⊔ W₂) =
        Module.finrank K W₃ := by
      omega
    exact Submodule.eq_of_le_of_finrank_le hle (by omega)

end Commons.LinearAlgebra.Submodule
