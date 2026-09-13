import Submission.Grassmann.Coords

/-!
# The counting identity of Proposition "taking restrictions of Laplacians"

arXiv:2209.04243 §8 (`lem:restrictiond of compositions of Laplacians`): for a linear map
`Y : W → V` whose kernel is contained in `W₁` and whose image contains `V₁` there is a *unique*
triple `(W₂,V₂,X)` with `W₂ ≥ W₁`, `V₂ ≤ V₁`, `X : W₂ → V/V₂` a linear map with kernel `W₁`,
image `V₁/V₂` and `X ≤ Y₂ = Y|_{W₂}^{V/V₂}`.

Equivalently, for every `Y : W → V`,

  `[V₁ ⊆ Im Y]·[ker Y ⊆ W₁] = Σ_{V₂ ≤ V₁} Σ_{W₂ ≥ W₁} #{X : W₂ → V/V₂ | ker X = W₁,
     Im X = V₁/V₂, X ≤ Y₂, and Y⁻¹(V₂) ⊆ W₂}`.

This combinatorial identity is the content of the proposition; it is what this file proves
(`sum_admCount`).  The proof uses the uniqueness of `(V₂,W₂)` (`W2sub_V2sub_unique`), the
uniqueness of `X` (proved here directly, `admX_unique`), and the fact that the canonical `Xlin`
realises the triple when `V₁ ≤ Im Y` and `ker Y ⊆ W₁`.
-/

open Finset BigOperators Matrix
open Classical

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

variable {m n : ℕ}

/-- The set of linear maps between two finite types is finite. -/
instance instFintypeLinearMap {M N : Type*} [Fintype M] [Fintype N] [AddCommGroup M]
    [Module 𝔽₂ M] [AddCommGroup N] [Module 𝔽₂ N] : Fintype (M →ₗ[𝔽₂] N) :=
  Fintype.ofInjective (fun f : M →ₗ[𝔽₂] N => (f : M → N))
    (fun f g h => LinearMap.ext (congrFun h))

/-- The admissible `X`'s for a fixed pair `(V₂,W₂)`: linear maps `X : ↥W₂ → V/V₂` with kernel
`W₁`, image `V₁/V₂`, lying below `Y₂ = Y|_{W₂}^{V/V₂}` in the rank order. -/
def CondX (V₁ V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Y : Matrix (Fin n) (Fin m) 𝔽₂) (X : ↥W₂ →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₂)) : Prop :=
  LinearMap.ker X = Submodule.comap W₂.subtype W₁ ∧
    LinearMap.range X = Submodule.map (Submodule.mkQ V₂) V₁ ∧
    lmLE X (YlinOf V₂ W₂ Y)

/-- **Uniqueness of the admissible `X`** (for `W₂ = W₁ + Y⁻¹(V₁)`, the only interesting case):
two linear maps `X, X' : ↥W₂ → V/V₂` with the same kernel `W₁`, the same image `V₁/V₂` and both
below `Y₂` in the rank order are equal. -/
theorem admX_unique (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Y : Matrix (Fin n) (Fin m) 𝔽₂) {V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)}
    {X X' : ↥(W2sub V₁ W₁ Y) →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₂)}
    (hX : CondX V₁ V₂ W₁ (W2sub V₁ W₁ Y) Y X)
    (hX' : CondX V₁ V₂ W₁ (W2sub V₁ W₁ Y) Y X') : X = X' := by
  have hrng : LinearMap.range X = LinearMap.range X' := by rw [hX.2.1, hX'.2.1]
  have h1 := (lmLE_iff X (YlinOf V₂ (W2sub V₁ W₁ Y) Y)).mp hX.2.2
  have h2 := (lmLE_iff X' (YlinOf V₂ (W2sub V₁ W₁ Y) Y)).mp hX'.2.2
  have hmemA : ∀ a : ↥(ASub V₁ Y),
      YlinOf V₂ (W2sub V₁ W₁ Y) Y ⟨a.1, (le_sup_left : ASub V₁ Y ≤ W2sub V₁ W₁ Y) a.2⟩ ∈
        LinearMap.range X := by
    intro a
    rw [hX.2.1]
    exact Submodule.mem_map.mpr ⟨Y.mulVecLin a.1, a.2, rfl⟩
  have hagree : ∀ a : ↥(ASub V₁ Y),
      X ⟨a.1, (le_sup_left : ASub V₁ Y ≤ W2sub V₁ W₁ Y) a.2⟩ =
        X' ⟨a.1, (le_sup_left : ASub V₁ Y ≤ W2sub V₁ W₁ Y) a.2⟩ := by
    intro a
    rw [← h1.2 _ (hmemA a), ← h2.2 _ (by rw [← hrng]; exact hmemA a)]
  have hzero : ∀ b : ↥(W2sub V₁ W₁ Y), (b : Fin m → 𝔽₂) ∈ W₁ → X b = 0 := by
    intro b hb
    rw [← LinearMap.mem_ker, hX.1]
    exact hb
  have hzero' : ∀ b : ↥(W2sub V₁ W₁ Y), (b : Fin m → 𝔽₂) ∈ W₁ → X' b = 0 := by
    intro b hb
    rw [← LinearMap.mem_ker, hX'.1]
    exact hb
  ext w
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (show (w : Fin m → 𝔽₂) ∈ W2sub V₁ W₁ Y from w.2)
  have haW : a ∈ W2sub V₁ W₁ Y := (le_sup_left : ASub V₁ Y ≤ W2sub V₁ W₁ Y) ha
  have hbW : b ∈ W2sub V₁ W₁ Y := (le_sup_right : W₁ ≤ W2sub V₁ W₁ Y) hb
  have hw : w = (⟨a, haW⟩ : ↥(W2sub V₁ W₁ Y)) + ⟨b, hbW⟩ :=
    Subtype.ext (by simpa using hab.symm)
  rw [hw, map_add, map_add, hagree ⟨a, ha⟩, hzero ⟨b, hbW⟩ hb, hzero' ⟨b, hbW⟩ hb]

/-- The number of admissible `X`'s for a fixed pair `(V₂,W₂)`. -/
def admCount (V₁ V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Y : Matrix (Fin n) (Fin m) 𝔽₂) : ℕ :=
  Nat.card {X : ↥W₂ →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₂) // CondX V₁ V₂ W₁ W₂ Y X}

/-- `admCount` vanishes when there is no admissible `X`. -/
theorem admCount_eq_zero_of_no (V₁ V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (Y : Matrix (Fin n) (Fin m) 𝔽₂)
    (h : ¬ ∃ X, CondX V₁ V₂ W₁ W₂ Y X) : admCount V₁ V₂ W₁ W₂ Y = 0 := by
  haveI : IsEmpty {X : ↥W₂ →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₂) // CondX V₁ V₂ W₁ W₂ Y X} :=
    ⟨fun x => h ⟨x.1, x.2⟩⟩
  rw [admCount, Nat.card_eq_zero]
  exact Or.inl inferInstance

/-- `admCount` is one when there is a (necessarily unique) admissible `X`. -/
theorem admCount_eq_one_of (V₁ V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (Y : Matrix (Fin n) (Fin m) 𝔽₂)
    (huniq : ∀ X X', CondX V₁ V₂ W₁ W₂ Y X → CondX V₁ V₂ W₁ W₂ Y X' → X = X')
    (h : ∃ X, CondX V₁ V₂ W₁ W₂ Y X) : admCount V₁ V₂ W₁ W₂ Y = 1 := by
  obtain ⟨X, hX⟩ := h
  haveI : Subsingleton {X : ↥W₂ →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₂) // CondX V₁ V₂ W₁ W₂ Y X} :=
    ⟨fun a b => Subtype.ext (huniq a.1 b.1 a.2 b.2)⟩
  rw [admCount, Nat.card_eq_one_iff_unique]
  exact ⟨inferInstance, ⟨⟨X, hX⟩⟩⟩

/-! ## The conditions imply `V₁ ≤ Im Y` and `ker Y ≤ W₁` -/

/-- If an admissible `X` exists for the pair `(V₂,W₂)` (with `V₂ ≤ V₁`, `W₁ ≤ W₂` and
`Y⁻¹(V₂) ⊆ W₂`) then automatically `V₁ ≤ Im Y` and `ker Y ≤ W₁`.  This is the key step that
makes the sum over `(V₂,W₂)` collapse. -/
theorem condX_imp (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Y : Matrix (Fin n) (Fin m) 𝔽₂) {V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)}
    {W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂)} (hV₂ : V₂ ≤ V₁) (hW₂ : W₁ ≤ W₂)
    (hhyb : hybridPredSub V₂ W₂ Y) {X : ↥W₂ →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₂)}
    (hX : CondX V₁ V₂ W₁ W₂ Y X) :
    V₁ ≤ LinearMap.range Y.mulVecLin ∧ LinearMap.ker Y.mulVecLin ≤ W₁ := by
  obtain ⟨hker, hrange, hle⟩ := hX
  have hle1 : LinearMap.range X ≤ LinearMap.range (YlinOf V₂ W₂ Y) := (lmLE_iff X _).mp hle |>.1
  have hle2 : ∀ w : ↥W₂, YlinOf V₂ W₂ Y w ∈ LinearMap.range X →
      YlinOf V₂ W₂ Y w = X w := (lmLE_iff X _).mp hle |>.2
  have hrangeY : LinearMap.range (YlinOf V₂ W₂ Y) =
      Submodule.map (Submodule.mkQ V₂) (Submodule.map Y.mulVecLin W₂) := by
    rw [YlinOf, LinearMap.range_comp, LinearMap.range_comp, Submodule.range_subtype]
  have hVle : V₁ ≤ Submodule.map Y.mulVecLin W₂ ⊔ V₂ := by
    refine le_sup_of_map_mkQ_le ?_
    rw [← hrangeY, ← hrange]
    exact hle1
  have hmapY : Submodule.map Y.mulVecLin W₂ ≤ LinearMap.range Y.mulVecLin :=
    LinearMap.map_le_range
  have hV : V₁ ≤ LinearMap.range Y.mulVecLin := fun v hv => by
    have hmem := hVle hv
    rw [Submodule.mem_sup] at hmem
    obtain ⟨a, ha, b, hb, hab⟩ := hmem
    rw [← hab]
    exact (LinearMap.range Y.mulVecLin).add_mem (hmapY ha) (hhyb.1 hb)
  refine ⟨hV, fun k hk => ?_⟩
  have hkY : Y.mulVecLin k = 0 := by
    rw [LinearMap.mem_ker] at hk; exact hk
  have hkW₂ : k ∈ W₂ := by
    refine hhyb.2 k ?_
    rw [← Matrix.mulVecLin_apply, hkY]
    exact V₂.zero_mem
  have hz : YlinOf V₂ W₂ Y ⟨k, hkW₂⟩ = 0 := by
    change Submodule.mkQ V₂ (Y.mulVecLin k) = 0
    rw [hkY, map_zero]
  have h0 : YlinOf V₂ W₂ Y ⟨k, hkW₂⟩ ∈ LinearMap.range X := by
    rw [hz]; exact Submodule.zero_mem _
  have hXk : X ⟨k, hkW₂⟩ = 0 := by rw [← hle2 ⟨k, hkW₂⟩ h0, hz]
  rw [← LinearMap.mem_ker, hker] at hXk
  exact hXk

/-- **`(V2sub, W2sub)` is always an admissible pair**: `Y⁻¹(V2sub) ⊆ W2sub` and
`V2sub ⊆ Im Y`. -/
theorem hybPredSub_V2sub_W2sub (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (Y : Matrix (Fin n) (Fin m) 𝔽₂) :
    hybridPredSub (V2sub V₁ W₁ Y) (W2sub V₁ W₁ Y) Y := by
  refine ⟨le_trans (show V2sub V₁ W₁ Y ≤ Submodule.map Y.mulVecLin W₁ from inf_le_left)
    (show Submodule.map Y.mulVecLin W₁ ≤ LinearMap.range Y.mulVecLin from
      LinearMap.map_le_range), fun w hw => ?_⟩
  have hw' : Y.mulVecLin w ∈ Submodule.map Y.mulVecLin W₁ :=
    (show V2sub V₁ W₁ Y ≤ Submodule.map Y.mulVecLin W₁ from inf_le_left) hw
  rw [Submodule.mem_map] at hw'
  obtain ⟨w', hw', hww'⟩ := hw'
  have hker : Y.mulVecLin (w - w') = 0 := by
    rw [map_sub, hww', sub_self]
  have hwsum : w = (w - w') + w' := by abel
  rw [hwsum]
  refine Submodule.mem_sup.mpr ⟨w - w', ?_, w', hw', rfl⟩
  show Y.mulVecLin (w - w') ∈ V₁
  rw [hker]
  exact V₁.zero_mem

/-- `admCount` vanishes unless `(V₂,W₂) = (V2sub, W2sub)`, provided `V₁ ≤ Im Y` (the case that
is used in the counting identity). -/
theorem admCount_eq_zero_of_ne (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (Y : Matrix (Fin n) (Fin m) 𝔽₂)
    (hV : V₁ ≤ LinearMap.range Y.mulVecLin) {V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)}
    {W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂)} (hV₂ : V₂ ≤ V₁) (hW₂ : W₁ ≤ W₂)
    (hhyb : hybridPredSub V₂ W₂ Y)
    (hne : ¬ (V₂ = V2sub V₁ W₁ Y ∧ W₂ = W2sub V₁ W₁ Y)) :
    admCount V₁ V₂ W₁ W₂ Y = 0 := by
  refine admCount_eq_zero_of_no V₁ V₂ W₁ W₂ Y (fun h => ?_)
  obtain ⟨X, hker, hrange, hle⟩ := h
  have hle1 : LinearMap.range X ≤ LinearMap.range (YlinOf V₂ W₂ Y) := (lmLE_iff X _).mp hle |>.1
  have hle2 : ∀ w : ↥W₂, YlinOf V₂ W₂ Y w ∈ LinearMap.range X →
      YlinOf V₂ W₂ Y w = X w := (lmLE_iff X _).mp hle |>.2
  have hle' : LinearMap.range X ≤
      LinearMap.range ((Submodule.mkQ V₂).comp (Y.mulVecLin.comp W₂.subtype)) := by
    rw [YlinOf] at hle1; exact hle1
  have hagree : ∀ w : ↥W₂, Y.mulVecLin w.1 ∈ V₁ →
      X w = Submodule.mkQ V₂ (Y.mulVecLin w.1) := by
    intro w hw
    have hmem : YlinOf V₂ W₂ Y w ∈ LinearMap.range X := by
      rw [hrange]
      exact Submodule.mem_map.mpr ⟨Y.mulVecLin w.1, hw, rfl⟩
    rw [← hle2 w hmem]
    rfl
  obtain ⟨hW2, hV2⟩ := W2sub_V2sub_unique hV hW₂ hV₂ (fun v hv => hhyb.2 v hv) hker hrange hle' hagree
  exact hne ⟨hV2, hW2⟩

/-- `admCount` vanishes when `V₁ ⊄ Im Y` or `ker Y ⊄ W₁`. -/
theorem admCount_eq_zero_of_not (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (Y : Matrix (Fin n) (Fin m) 𝔽₂)
    (h : ¬ (V₁ ≤ LinearMap.range Y.mulVecLin ∧ LinearMap.ker Y.mulVecLin ≤ W₁))
    {V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)} {W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂)}
    (hV₂ : V₂ ≤ V₁) (hW₂ : W₁ ≤ W₂) (hhyb : hybridPredSub V₂ W₂ Y) :
    admCount V₁ V₂ W₁ W₂ Y = 0 :=
  admCount_eq_zero_of_no V₁ V₂ W₁ W₂ Y (fun hex =>
    h (condX_imp V₁ W₁ Y hV₂ hW₂ hhyb hex.choose_spec))

/-- `admCount` equals one at the canonical pair `(V2sub, W2sub)` when the character is kept. -/
theorem admCount_eq_one (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Y : Matrix (Fin n) (Fin m) 𝔽₂) (hV : V₁ ≤ LinearMap.range Y.mulVecLin)
    (hW : LinearMap.ker Y.mulVecLin ≤ W₁) :
    admCount V₁ (V2sub V₁ W₁ Y) W₁ (W2sub V₁ W₁ Y) Y = 1 := by
  have hmem : CondX V₁ (V2sub V₁ W₁ Y) W₁ (W2sub V₁ W₁ Y) Y (Xlin V₁ W₁ Y) :=
    ⟨ker_Xlin hW, range_Xlin hV, lmLE_Xlin V₁ W₁ hV hW⟩
  exact admCount_eq_one_of V₁ (V2sub V₁ W₁ Y) W₁ (W2sub V₁ W₁ Y) Y
    (fun X X' h1 h2 => admX_unique V₁ W₁ Y h1 h2) ⟨Xlin V₁ W₁ Y, hmem⟩

/-- `admCount` as a sum of indicators. -/
theorem admCount_eq_sum (V₁ V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (Y : Matrix (Fin n) (Fin m) 𝔽₂) :
    (admCount V₁ V₂ W₁ W₂ Y : ℂ) =
      ∑ X : ↥W₂ →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₂),
        (if CondX V₁ V₂ W₁ W₂ Y X then (1 : ℂ) else 0) := by
  rw [admCount, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter,
    Nat.cast_sum]
  refine Finset.sum_congr rfl (fun X _ => ?_)
  by_cases hX : CondX V₁ V₂ W₁ W₂ Y X <;> simp [hX]

/-! ## The counting identity -/

/-- **The counting identity** of `lem:restrictiond of compositions of Laplacians`:
the number of triples `(V₂,W₂,X)` with `V₂ ≤ V₁`, `W₂ ≥ W₁`, `Y⁻¹(V₂) ⊆ W₂`,
`ker X = W₁`, `Im X = V₁/V₂` and `X ≤ Y|_{W₂}^{V/V₂}` is `1` if `V₁ ⊆ Im Y` and `ker Y ⊆ W₁`,
and `0` otherwise. -/
theorem sum_admCount (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Y : Matrix (Fin n) (Fin m) 𝔽₂) :
    (∑ p : Submodule 𝔽₂ (Fin n → 𝔽₂) × Submodule 𝔽₂ (Fin m → 𝔽₂),
        (if p.1 ≤ V₁ ∧ W₁ ≤ p.2 ∧ hybridPredSub p.1 p.2 Y then
          (admCount V₁ p.1 W₁ p.2 Y : ℂ) else 0)) =
      if V₁ ≤ LinearMap.range Y.mulVecLin ∧ LinearMap.ker Y.mulVecLin ≤ W₁ then 1 else 0 := by
  by_cases h : V₁ ≤ LinearMap.range Y.mulVecLin ∧ LinearMap.ker Y.mulVecLin ≤ W₁
  · rw [if_pos h]
    have hterm : ∀ p : Submodule 𝔽₂ (Fin n → 𝔽₂) × Submodule 𝔽₂ (Fin m → 𝔽₂),
        (if p.1 ≤ V₁ ∧ W₁ ≤ p.2 ∧ hybridPredSub p.1 p.2 Y then
            (admCount V₁ p.1 W₁ p.2 Y : ℂ) else 0) =
          (if p = (V2sub V₁ W₁ Y, W2sub V₁ W₁ Y) then (1 : ℂ) else 0) := by
      rintro ⟨V₂, W₂⟩
      by_cases hc : V₂ ≤ V₁ ∧ W₁ ≤ W₂ ∧ hybridPredSub V₂ W₂ Y
      · rw [if_pos hc]
        by_cases heq : (V₂, W₂) = (V2sub V₁ W₁ Y, W2sub V₁ W₁ Y)
        · rw [if_pos heq]
          have h1 : V₂ = V2sub V₁ W₁ Y := congrArg Prod.fst heq
          have h2 : W₂ = W2sub V₁ W₁ Y := congrArg Prod.snd heq
          rw [h1, h2, admCount_eq_one V₁ W₁ Y h.1 h.2]
          norm_num
        · rw [if_neg heq, admCount_eq_zero_of_ne V₁ W₁ Y h.1 hc.1 hc.2.1 hc.2.2
            (fun hh => heq (by rw [hh.1, hh.2]))]
          norm_num
      · rw [if_neg hc]
        rw [if_neg (fun heq => hc (by
          have h1 : V₂ = V2sub V₁ W₁ Y := congrArg Prod.fst heq
          have h2 : W₂ = W2sub V₁ W₁ Y := congrArg Prod.snd heq
          rw [h1, h2]
          exact ⟨V2sub_le V₁ W₁ Y, le_W2sub V₁ W₁ Y, hybPredSub_V2sub_W2sub V₁ W₁ Y⟩))]
    rw [Finset.sum_congr rfl fun p _ => hterm p]
    exact Fintype.sum_ite_eq' (V2sub V₁ W₁ Y, W2sub V₁ W₁ Y) (fun _ => (1 : ℂ))
  · rw [if_neg h]
    refine Finset.sum_eq_zero (fun p _ => ?_)
    by_cases hc : p.1 ≤ V₁ ∧ W₁ ≤ p.2 ∧ hybridPredSub p.1 p.2 Y
    · rw [if_pos hc, admCount_eq_zero_of_not V₁ W₁ Y h hc.1 hc.2.1 hc.2.2]
      norm_num
    · rw [if_neg hc]

/-- The counting identity in nested form. -/
theorem sum_admCount_nested (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Y : Matrix (Fin n) (Fin m) 𝔽₂) :
    (∑ V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂),
        (if V₂ ≤ V₁ ∧ W₁ ≤ W₂ ∧ hybridPredSub V₂ W₂ Y then
          (admCount V₁ V₂ W₁ W₂ Y : ℂ) else 0)) =
      if V₁ ≤ LinearMap.range Y.mulVecLin ∧ LinearMap.ker Y.mulVecLin ≤ W₁ then 1 else 0 := by
  rw [← Fintype.sum_prod_type (fun p : Submodule 𝔽₂ (Fin n → 𝔽₂) × Submodule 𝔽₂ (Fin m → 𝔽₂) =>
    (if p.1 ≤ V₁ ∧ W₁ ≤ p.2 ∧ hybridPredSub p.1 p.2 Y then (admCount V₁ p.1 W₁ p.2 Y : ℂ)
      else 0))]
  exact sum_admCount V₁ W₁ Y

end

end Submission.Grassmann
