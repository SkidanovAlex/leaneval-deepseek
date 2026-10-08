import Mathlib
import Submission.Work.Hering.GL32.AppIXSurj
import Submission.Work.Hering.GL32.AppIXK4
import Submission.Work.Hering.GL32.AppIXTheta
import Submission.Work.Hering.GL32.AppIXNatIrreducible
import Submission.Work.Hering.GL32.rad_irreducible

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Appendix IX: assembling the classification

Given a finite simple `F₂[GL(3,2)]`-module `M`, the Frobenius step produces a surjective
`GL(3,2)`-equivariant map `ψ : W ↠ M` (`W` the permutation module on the `21` pairs).  This file
contains the linear algebra of the final step:

* the action `Phi g` of `GL(3,2)` on the target `k × V × V* × M₄` of `combinedMap`, and the
  equivariance `combinedMap (actW g f) = Phi g (combinedMap f)`;
* a splitting `sec` of `combinedMap` and the induced map `T : k × V × V* × M₄ → M`, which is
  `GL(3,2)`-equivariant as soon as `K₄ ≤ ker ψ`;
* the resulting classification: a nonzero simple `M` with such a `ψ` is isomorphic to one of the
  four factors, hence has `F₂`-dimension `1`, `3` or `8`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

namespace Work.Hering.GL32

/-- The target of `combinedMap`. -/
abbrev Tgt : Type := ZMod 2 × F2v × Module.Dual (ZMod 2) F2v × M4

/-- The action of `GL(3,2)` on the target of `combinedMap`. -/
noncomputable def Phi (g : GL32) (x : Tgt) : Tgt :=
  (x.1, g x.2.1, (g.symm : GL32).dualMap x.2.2.1,
    ⟨conjMat g ((x.2.2.2 : M4) : Mat3), by rw [mem_M4_iff, conjMat_trace]; exact (x.2.2.2).2⟩)

/-- `combinedMap` is equivariant for the action `Phi`. -/
lemma combinedMap_Phi (g : GL32) (f : W) : combinedMap (actW g f) = Phi g (combinedMap f) := by
  simp only [combinedMap, LinearMap.prod_apply, Phi]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · exact aug_actW g f
  · exact phi_actW g f
  · exact psi_actW g f
  · exact Subtype.ext (theta_actW g f)

/-! ## The splitting of `combinedMap` -/

/-- A linear splitting of `combinedMap`. -/
noncomputable def sec (x : Tgt) : W := Classical.choose (combined_surjective x)

lemma combinedMap_sec (x : Tgt) : combinedMap (sec x) = x :=
  Classical.choose_spec (combined_surjective x)

lemma sec_diff_mem_K4 {x y : W} (h : combinedMap x = combinedMap y) : x - y ∈ K4 := by
  rw [K4, LinearMap.mem_ker, map_sub, h, sub_self]

lemma psi_eq_of_K4 {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (ψ : W →ₗ[ZMod 2] M)
    (hK4 : K4 ≤ LinearMap.ker ψ) {x y : W} (h : x - y ∈ K4) : ψ x = ψ y := by
  have h2 : ψ (x - y) = 0 := by
    have := hK4 h
    rwa [LinearMap.mem_ker] at this
  rwa [map_sub, sub_eq_zero] at h2

/-- The map induced by `ψ` on the target of `combinedMap` (well defined because `K₄ ≤ ker ψ`). -/
noncomputable def Tfun {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (ψ : W →ₗ[ZMod 2] M)
    (x : Tgt) : M := ψ (sec x)

lemma Tfun_add {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (ψ : W →ₗ[ZMod 2] M)
    (hK4 : K4 ≤ LinearMap.ker ψ) (x y : Tgt) : Tfun ψ (x + y) = Tfun ψ x + Tfun ψ y := by
  have h : sec (x + y) - (sec x + sec y) ∈ K4 := by
    rw [K4, LinearMap.mem_ker, map_sub, map_add, combinedMap_sec, combinedMap_sec,
      combinedMap_sec, sub_self]
  show ψ (sec (x + y)) = ψ (sec x) + ψ (sec y)
  rw [psi_eq_of_K4 ψ hK4 h, map_add]

lemma Tfun_smul {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (ψ : W →ₗ[ZMod 2] M)
    (hK4 : K4 ≤ LinearMap.ker ψ) (c : ZMod 2) (x : Tgt) : Tfun ψ (c • x) = c • Tfun ψ x := by
  have h : sec (c • x) - c • sec x ∈ K4 := by
    rw [K4, LinearMap.mem_ker, map_sub, map_smul, combinedMap_sec, combinedMap_sec, sub_self]
  show ψ (sec (c • x)) = c • ψ (sec x)
  rw [psi_eq_of_K4 ψ hK4 h, map_smul]

/-- The `ZMod 2`-linear map induced by `ψ`. -/
noncomputable def T {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (ψ : W →ₗ[ZMod 2] M)
    (hK4 : K4 ≤ LinearMap.ker ψ) : Tgt →ₗ[ZMod 2] M where
  toFun := Tfun ψ
  map_add' := Tfun_add ψ hK4
  map_smul' := Tfun_smul ψ hK4

lemma T_apply {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (ψ : W →ₗ[ZMod 2] M)
    (hK4 : K4 ≤ LinearMap.ker ψ) (x : Tgt) : T ψ hK4 x = ψ (sec x) := rfl

/-- `T` is equivariant for the action `Phi` on the target. -/
lemma T_Phi {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (ρ : GL32 →* (M ≃ₗ[ZMod 2] M))
    (ψ : W →ₗ[ZMod 2] M) (hψ : ∀ g f, ψ (actW g f) = ρ g (ψ f)) (hK4 : K4 ≤ LinearMap.ker ψ)
    (g : GL32) (x : Tgt) : T ψ hK4 (Phi g x) = ρ g (T ψ hK4 x) := by
  have h : sec (Phi g x) - actW g (sec x) ∈ K4 := by
    rw [K4, LinearMap.mem_ker, map_sub, combinedMap_sec, combinedMap_Phi, combinedMap_sec,
      sub_self]
  have h2 := psi_eq_of_K4 ψ hK4 h
  rw [T_apply, T_apply, h2, hψ]

/-- `T` is surjective whenever `ψ` is. -/
lemma T_surjective {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (ψ : W →ₗ[ZMod 2] M)
    (hK4 : K4 ≤ LinearMap.ker ψ) (hsurj : Function.Surjective ψ) :
    Function.Surjective (T ψ hK4) := by
  intro m
  obtain ⟨y, hy⟩ := hsurj m
  refine ⟨combinedMap y, ?_⟩
  have h : sec (combinedMap y) - y ∈ K4 := sec_diff_mem_K4 (by rw [combinedMap_sec])
  have h2 := psi_eq_of_K4 ψ hK4 h
  rw [T_apply, ← hy]
  exact h2

/-! ## A nonzero equivariant map out of a simple source is bijective -/

lemma bijective_of_invariant {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (ρ : GL32 →* (M ≃ₗ[ZMod 2] M)) {A : Type*} [AddCommGroup A]
    [Module (ZMod 2) A] (act : GL32 → A → A) (f : A →ₗ[ZMod 2] M)
    (hf : ∀ g a, f (act g a) = ρ g (f a))
    (hcl : ∀ S : Submodule (ZMod 2) A, (∀ g a, a ∈ S → act g a ∈ S) → S = ⊥ ∨ S = ⊤)
    (hne : f ≠ 0)
    (hsimple : ∀ W' : Submodule (ZMod 2) M, (∀ g, ∀ w ∈ W', ρ g w ∈ W') → W' = ⊥ ∨ W' = ⊤) :
    Function.Bijective f := by
  constructor
  · have hInv : ∀ g a, a ∈ LinearMap.ker f → act g a ∈ LinearMap.ker f := by
      intro g a ha
      rw [LinearMap.mem_ker] at ha ⊢
      rw [hf, ha, map_zero]
    rcases hcl _ hInv with h | h
    · exact LinearMap.ker_eq_bot.mp h
    · exact absurd (LinearMap.ker_eq_top.mp h) hne
  · have hInv : ∀ g w, w ∈ LinearMap.range f → ρ g w ∈ LinearMap.range f := by
      rintro g w ⟨a, rfl⟩
      exact ⟨act g a, hf g a⟩
    rcases hsimple _ hInv with h | h
    · exact absurd (by rwa [LinearMap.range_eq_bot] at h) hne
    · exact LinearMap.range_eq_top.mp h

/-! ## The four coordinate inclusions -/

/-- The inclusion of the `k`-component of the target. -/
noncomputable def inclK : ZMod 2 →ₗ[ZMod 2] Tgt where
  toFun c := (c, 0, 0, 0)
  map_add' := by intro a b; ext <;> simp
  map_smul' := by intro c a; ext <;> simp

/-- The inclusion of the `V`-component of the target. -/
noncomputable def inclV : F2v →ₗ[ZMod 2] Tgt where
  toFun v := (0, v, 0, 0)
  map_add' := by intro a b; ext <;> simp
  map_smul' := by intro c a; ext <;> simp

/-- The inclusion of the `V*`-component of the target. -/
noncomputable def inclD : Module.Dual (ZMod 2) F2v →ₗ[ZMod 2] Tgt where
  toFun s := (0, 0, s, 0)
  map_add' := by intro a b; ext <;> simp
  map_smul' := by intro c a; ext <;> simp

/-- The inclusion of the `M₄`-component of the target. -/
noncomputable def inclM : M4 →ₗ[ZMod 2] Tgt where
  toFun A := (0, 0, 0, A)
  map_add' := by intro a b; ext <;> simp
  map_smul' := by intro c a; ext <;> simp

lemma Phi_inclK (g : GL32) (c : ZMod 2) : Phi g (inclK c) = inclK c := by
  ext <;> simp [Phi, inclK, conjMat_zero]

lemma Phi_inclV (g : GL32) (v : F2v) : Phi g (inclV v) = inclV (g v) := by
  ext <;> simp [Phi, inclV, conjMat_zero]

lemma Phi_inclD (g : GL32) (s : Module.Dual (ZMod 2) F2v) :
    Phi g (inclD s) = inclD ((g.symm : GL32).dualMap s) := by
  ext <;> simp [Phi, inclD, conjMat_zero]

lemma Phi_inclM (g : GL32) (A : M4) :
    Phi g (inclM A) = inclM
      (⟨conjMat g ((A : M4) : Mat3), by rw [mem_M4_iff, conjMat_trace]; exact A.2⟩ : M4) := by
  ext <;> simp [Phi, inclM]

/-- The four coordinate projections add up to the identity of the target. -/
lemma decomposition (x : Tgt) :
    x = inclK x.1 + inclV x.2.1 + inclD x.2.2.1 + inclM x.2.2.2 := by
  ext <;> simp [inclK, inclV, inclD, inclM]


/-! ## The four simplicity statements in "invariant submodule" form -/

lemma zmod2_eq_zero_or_one (y : ZMod 2) : y = 0 ∨ y = 1 := by
  revert y; decide

lemma symm_inv_symm (g : GL32) : (((g⁻¹ : GL32).symm : GL32)) = g := by
  rw [show (g⁻¹ : GL32) = g.symm from rfl, LinearEquiv.symm_symm]

lemma classification_K (S : Submodule (ZMod 2) (ZMod 2))
    (h : ∀ (g : GL32) (a : ZMod 2), a ∈ S → a ∈ S) : S = ⊥ ∨ S = ⊤ := by
  by_cases hbot : S = ⊥
  · exact Or.inl hbot
  · right
    obtain ⟨y, hyS, hy0⟩ := (Submodule.ne_bot_iff S).mp hbot
    have hy1 : y = 1 := (zmod2_eq_zero_or_one y).resolve_left hy0
    rw [Submodule.eq_top_iff']
    intro x
    have hy1S : (1 : ZMod 2) ∈ S := by rw [← hy1]; exact hyS
    have hx := S.smul_mem (x : ZMod 2) hy1S
    rwa [smul_eq_mul, mul_one] at hx

lemma classification_V (S : Submodule (ZMod 2) F2v)
    (h : ∀ (g : GL32) (v : F2v), v ∈ S → g v ∈ S) : S = ⊥ ∨ S = ⊤ :=
  nat_irreducible S h

lemma classification_D (S : Submodule (ZMod 2) (Module.Dual (ZMod 2) F2v))
    (h : ∀ (g : GL32) (s : Module.Dual (ZMod 2) F2v), s ∈ S → (g.symm : GL32).dualMap s ∈ S) :
    S = ⊥ ∨ S = ⊤ := by
  refine dual_irreducible S ?_
  intro g s hs
  have h1 := h g⁻¹ s hs
  rwa [symm_inv_symm g] at h1

lemma classification_M (S : Submodule (ZMod 2) M4)
    (h : ∀ (g : GL32) (A : M4), A ∈ S →
      (⟨conjMat g ((A : M4) : Mat3), by rw [mem_M4_iff, conjMat_trace]; exact A.2⟩ : M4) ∈ S) :
    S = ⊥ ∨ S = ⊤ := by
  have htr : ∀ A ∈ S.map M4.subtype, A.trace = 0 := by
    intro A hA
    obtain ⟨B, -, rfl⟩ := Submodule.mem_map.mp hA
    exact B.2
  have hinv : ∀ (g : GL32) (A : Mat3), A ∈ S.map M4.subtype →
      (LinearMap.toMatrix' (g : F2v →ₗ[ZMod 2] F2v)) * A *
        (LinearMap.toMatrix' ((g.symm : GL32) : F2v →ₗ[ZMod 2] F2v)) ∈ S.map M4.subtype := by
    intro g A hA
    obtain ⟨B, hB, rfl⟩ := Submodule.mem_map.mp hA
    exact Submodule.mem_map.mpr ⟨_, h g B hB, rfl⟩
  rcases rad_irreducible (S.map M4.subtype) htr hinv with hbot | htop
  · left
    rw [Submodule.eq_bot_iff]
    intro A hA
    have h1 : (A : Mat3) ∈ S.map M4.subtype := Submodule.mem_map.mpr ⟨A, hA, rfl⟩
    rw [hbot] at h1
    simpa using h1
  · right
    rw [Submodule.eq_top_iff']
    intro A
    have h1 : (A : Mat3) ∈ S.map M4.subtype := htop _ A.2
    obtain ⟨B, hB, hAB⟩ := Submodule.mem_map.mp h1
    rw [← (Subtype.ext_iff).mpr hAB]
    exact hB

/-! ## The three cases -/

/-- Case 1: `ψ ∘ phiStar ≠ 0`, so `M` is the simple module `V*` of dimension `3`. -/
lemma finrank_eq_of_phiStar_ne {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (ρ : GL32 →* (M ≃ₗ[ZMod 2] M))
    (hsimple : ∀ W' : Submodule (ZMod 2) M, (∀ g, ∀ w ∈ W', ρ g w ∈ W') → W' = ⊥ ∨ W' = ⊤)
    (ψ : W →ₗ[ZMod 2] M) (hψ : ∀ g f, ψ (actW g f) = ρ g (ψ f))
    (h1 : ψ.comp phiStar ≠ 0) :
    Module.finrank (ZMod 2) M = 1 ∨ Module.finrank (ZMod 2) M = 3 ∨
      Module.finrank (ZMod 2) M = 8 := by
  have hf_act : ∀ (g : GL32) (s : Module.Dual (ZMod 2) F2v),
      (ψ.comp phiStar) ((g.symm : GL32).dualMap s) = ρ g ((ψ.comp phiStar) s) := by
    intro g s
    rw [LinearMap.comp_apply, phiStar_actVstar g s, hψ g (phiStar s), LinearMap.comp_apply]
  have hInv : DualInvariant (LinearMap.ker (ψ.comp phiStar)) := by
    intro g s hs
    rw [LinearMap.mem_ker] at hs ⊢
    have h := hf_act g⁻¹ s
    rw [hs, map_zero, symm_inv_symm g] at h
    exact h
  rcases dual_irreducible _ hInv with hbot | htop
  · have hinj : Function.Injective (ψ.comp phiStar) := LinearMap.ker_eq_bot.mp hbot
    have hinv : ∀ (g : GL32) (w : M), w ∈ LinearMap.range (ψ.comp phiStar) →
        ρ g w ∈ LinearMap.range (ψ.comp phiStar) := by
      rintro g w ⟨s, rfl⟩
      exact ⟨(g.symm : GL32).dualMap s, hf_act g s⟩
    rcases hsimple _ hinv with h | h
    · exact absurd (LinearMap.range_eq_bot.mp h) h1
    · have e : Module.Dual (ZMod 2) F2v ≃ₗ[ZMod 2] M :=
        LinearEquiv.ofBijective _ ⟨hinj, LinearMap.range_eq_top.mp h⟩
      exact Or.inr (Or.inl (by rw [← LinearEquiv.finrank_eq e, finrank_dual]))
  · exact absurd (LinearMap.ker_eq_top.mp htop) h1

/-- Case 2: `ψ ∘ phiStar = 0 ≠ ψ ∘ psiStar`, so `M` is the natural module `V` of dimension `3`. -/
lemma finrank_eq_of_psiStar_ne {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (ρ : GL32 →* (M ≃ₗ[ZMod 2] M))
    (hsimple : ∀ W' : Submodule (ZMod 2) M, (∀ g, ∀ w ∈ W', ρ g w ∈ W') → W' = ⊥ ∨ W' = ⊤)
    (ψ : W →ₗ[ZMod 2] M) (hψ : ∀ g f, ψ (actW g f) = ρ g (ψ f))
    (h2 : ψ.comp psiStar ≠ 0) :
    Module.finrank (ZMod 2) M = 1 ∨ Module.finrank (ZMod 2) M = 3 ∨
      Module.finrank (ZMod 2) M = 8 := by
  have hf_act : ∀ (g : GL32) (v : F2v), (ψ.comp psiStar) (g v) = ρ g ((ψ.comp psiStar) v) := by
    intro g v
    rw [LinearMap.comp_apply, psiStar_actV g v, hψ g (psiStar v), LinearMap.comp_apply]
  have hInv : ∀ (g : GL32) (v : F2v),
      v ∈ LinearMap.ker (ψ.comp psiStar) → g v ∈ LinearMap.ker (ψ.comp psiStar) := by
    intro g v hv
    rw [LinearMap.mem_ker] at hv ⊢
    rw [hf_act, hv, map_zero]
  rcases nat_irreducible _ hInv with hbot | htop
  · have hinj : Function.Injective (ψ.comp psiStar) := LinearMap.ker_eq_bot.mp hbot
    have hinv : ∀ (g : GL32) (w : M), w ∈ LinearMap.range (ψ.comp psiStar) →
        ρ g w ∈ LinearMap.range (ψ.comp psiStar) := by
      rintro g w ⟨v, rfl⟩
      exact ⟨g v, hf_act g v⟩
    rcases hsimple _ hinv with h | h
    · exact absurd (LinearMap.range_eq_bot.mp h) h2
    · have e : F2v ≃ₗ[ZMod 2] M :=
        LinearEquiv.ofBijective _ ⟨hinj, LinearMap.range_eq_top.mp h⟩
      exact Or.inr (Or.inl (by rw [← LinearEquiv.finrank_eq e, finrank_F2v]))
  · exact absurd (LinearMap.ker_eq_top.mp htop) h2

/-- Case 3: `ψ` vanishes on both `phiStar` and `psiStar`, so `K₄ ≤ ker ψ` and `M` is a quotient of
`k × V × V* × M₄`; by the four simplicity statements it is one of the four factors. -/
lemma finrank_eq_of_K4_le {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (ρ : GL32 →* (M ≃ₗ[ZMod 2] M)) (hne : ∃ m : M, m ≠ 0)
    (hsimple : ∀ W' : Submodule (ZMod 2) M, (∀ g, ∀ w ∈ W', ρ g w ∈ W') → W' = ⊥ ∨ W' = ⊤)
    (ψ : W →ₗ[ZMod 2] M) (hsurj : Function.Surjective ψ)
    (hψ : ∀ g f, ψ (actW g f) = ρ g (ψ f)) (hK4 : K4 ≤ LinearMap.ker ψ) :
    Module.finrank (ZMod 2) M = 1 ∨ Module.finrank (ZMod 2) M = 3 ∨
      Module.finrank (ZMod 2) M = 8 := by
  have hTsurj : Function.Surjective (T ψ hK4) := T_surjective ψ hK4 hsurj
  have hTne : T ψ hK4 ≠ 0 := by
    intro h0
    obtain ⟨m, hm⟩ := hne
    obtain ⟨x, hx⟩ := hTsurj m
    rw [h0, LinearMap.zero_apply] at hx
    exact hm hx.symm
  let fK : ZMod 2 →ₗ[ZMod 2] M := (T ψ hK4).comp inclK
  let fV : F2v →ₗ[ZMod 2] M := (T ψ hK4).comp inclV
  let fD : Module.Dual (ZMod 2) F2v →ₗ[ZMod 2] M := (T ψ hK4).comp inclD
  let fM : M4 →ₗ[ZMod 2] M := (T ψ hK4).comp inclM
  have hsome : fK ≠ 0 ∨ fV ≠ 0 ∨ fD ≠ 0 ∨ fM ≠ 0 := by
    by_contra h
    push_neg at h
    obtain ⟨hK, hV, hD, hM⟩ := h
    have hK' : ∀ c : ZMod 2, T ψ hK4 (inclK c) = 0 :=
      fun c => by simpa [fK] using congrFun (congrArg DFunLike.coe hK) c
    have hV' : ∀ v : F2v, T ψ hK4 (inclV v) = 0 :=
      fun v => by simpa [fV] using congrFun (congrArg DFunLike.coe hV) v
    have hD' : ∀ s : Module.Dual (ZMod 2) F2v, T ψ hK4 (inclD s) = 0 :=
      fun s => by simpa [fD] using congrFun (congrArg DFunLike.coe hD) s
    have hM' : ∀ A : M4, T ψ hK4 (inclM A) = 0 :=
      fun A => by simpa [fM] using congrFun (congrArg DFunLike.coe hM) A
    exact hTne (by
      apply LinearMap.ext
      intro x
      rw [decomposition x, map_add, map_add, map_add, LinearMap.zero_apply, hK', hV', hD', hM']
      simp)
  rcases hsome with h | h | h | h
  · have hf : ∀ (g : GL32) (c : ZMod 2), fK ((fun _ c => c) g c) = ρ g (fK c) := by
      intro g c
      show T ψ hK4 (inclK c) = ρ g (T ψ hK4 (inclK c))
      rw [← T_Phi ρ ψ hψ hK4 g (inclK c), Phi_inclK]
    have e : ZMod 2 ≃ₗ[ZMod 2] M :=
      LinearEquiv.ofBijective _ (bijective_of_invariant ρ _ fK hf classification_K h hsimple)
    exact Or.inl (by rw [← LinearEquiv.finrank_eq e, Module.finrank_self])
  · have hf : ∀ (g : GL32) (v : F2v), fV (g v) = ρ g (fV v) := by
      intro g v
      show T ψ hK4 (inclV (g v)) = ρ g (T ψ hK4 (inclV v))
      rw [← Phi_inclV g v, T_Phi ρ ψ hψ hK4]
    have e : F2v ≃ₗ[ZMod 2] M :=
      LinearEquiv.ofBijective _ (bijective_of_invariant ρ _ fV hf classification_V h hsimple)
    exact Or.inr (Or.inl (by rw [← LinearEquiv.finrank_eq e, finrank_F2v]))
  · have hf : ∀ (g : GL32) (s : Module.Dual (ZMod 2) F2v),
        fD ((g.symm : GL32).dualMap s) = ρ g (fD s) := by
      intro g s
      show T ψ hK4 (inclD ((g.symm : GL32).dualMap s)) = ρ g (T ψ hK4 (inclD s))
      rw [← Phi_inclD g s, T_Phi ρ ψ hψ hK4]
    have e : Module.Dual (ZMod 2) F2v ≃ₗ[ZMod 2] M :=
      LinearEquiv.ofBijective _ (bijective_of_invariant ρ _ fD hf classification_D h hsimple)
    exact Or.inr (Or.inl (by rw [← LinearEquiv.finrank_eq e, finrank_dual]))
  · have hf : ∀ (g : GL32) (A : M4),
        fM (⟨conjMat g ((A : M4) : Mat3), by rw [mem_M4_iff, conjMat_trace]; exact A.2⟩ : M4) =
          ρ g (fM A) := by
      intro g A
      show T ψ hK4 (inclM _) = ρ g (T ψ hK4 (inclM A))
      rw [← Phi_inclM g A, T_Phi ρ ψ hψ hK4]
    have e : M4 ≃ₗ[ZMod 2] M :=
      LinearEquiv.ofBijective _ (bijective_of_invariant ρ _ fM hf classification_M h hsimple)
    exact Or.inr (Or.inr (by rw [← LinearEquiv.finrank_eq e, finrank_M4]))

end Work.Hering.GL32
