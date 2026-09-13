import Mathlib
import Submission.Commons.LinearAlgebra.Submodule.card_inf_bot_ge_quarter
import Submission.Commons.LinearAlgebra.Dimension.finrank_map_eq_finrank_sub_finrank_inf_ker

open Module

namespace Commons.LinearAlgebra.Submodule

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Bijection between submodules `U` of `V` with `A ≤ U ≤ B` and all submodules of the
quotient `B ⧸ A`, realised as `Submodule.map A.mkQ B`.  The forward map sends `U` to the
submodule `(U/A) ⊓ (B/A)` of `B/A`; the inverse sends `W ≤ B/A` to
`comap A.mkQ (map B'.subtype W)`. -/
noncomputable def intervalEquiv (A B : Submodule K V) (hAB : A ≤ B) :
    {U : Submodule K V // A ≤ U ∧ U ≤ B} ≃ Submodule K ↥(Submodule.map A.mkQ B) where
  toFun U := Submodule.comap (Submodule.map A.mkQ B).subtype (Submodule.map A.mkQ U.1)
  invFun W := ⟨Submodule.comap A.mkQ (Submodule.map (Submodule.map A.mkQ B).subtype W),
    Submodule.le_comap_mkQ A _,
    (Submodule.comap_mono (Submodule.map_subtype_le _ _)).trans (le_of_eq (by
      rw [Submodule.comap_map_mkQ, sup_eq_right.mpr hAB]))⟩
  left_inv U := by
    apply Subtype.ext
    show Submodule.comap A.mkQ
        (Submodule.map (Submodule.map A.mkQ B).subtype
          (Submodule.comap (Submodule.map A.mkQ B).subtype (Submodule.map A.mkQ U.1))) = U.1
    rw [Submodule.map_comap_subtype]
    have hX : Submodule.map A.mkQ U.1 ≤ Submodule.map A.mkQ B := Submodule.map_mono U.2.2
    rw [inf_eq_right.mpr hX]
    rw [Submodule.comap_map_eq, Submodule.ker_mkQ, sup_eq_left.mpr U.2.1]
  right_inv W := by
    show Submodule.comap (Submodule.map A.mkQ B).subtype
      (Submodule.map A.mkQ (Submodule.comap A.mkQ
        (Submodule.map (Submodule.map A.mkQ B).subtype W))) = W
    rw [Submodule.map_comap_eq, Submodule.range_mkQ, top_inf_eq]
    exact Submodule.comap_map_eq_of_injective (Submodule.map A.mkQ B).subtype_injective W

/-- The dimension of the submodule of `B ⧸ A` corresponding to `U` is
`finrank U - finrank A`. -/
theorem intervalEquiv_finrank [Module.Finite K V]
    (A B : Submodule K V) (hAB : A ≤ B)
    (U : {U : Submodule K V // A ≤ U ∧ U ≤ B}) :
    Module.finrank K ↥(intervalEquiv A B hAB U)
      = Module.finrank K ↥U.1 - Module.finrank K A := by
  have hXle : Submodule.map A.mkQ U.1 ≤ Submodule.map A.mkQ B := Submodule.map_mono U.2.2
  have h1 : Module.finrank K ↥(Submodule.comap (Submodule.map A.mkQ B).subtype
        (Submodule.map A.mkQ U.1)) = Module.finrank K ↥(Submodule.map A.mkQ U.1) :=
    (Submodule.comapSubtypeEquivOfLe hXle).finrank_eq
  have h2 : Module.finrank K ↥(Submodule.map A.mkQ U.1)
      = Module.finrank K ↥(U.1) - Module.finrank K ↥(U.1 ⊓ A.mkQ.ker) :=
    Commons.LinearAlgebra.Dimension.finrank_map_eq_finrank_sub_finrank_inf_ker (A.mkQ) U.1
  show Module.finrank K ↥(Submodule.comap (Submodule.map A.mkQ B).subtype
        (Submodule.map A.mkQ U.1)) = Module.finrank K ↥U.1 - Module.finrank K A
  rw [h1, h2, Submodule.ker_mkQ, inf_eq_right.mpr U.2.1]

/-- `U ⊓ L = ⊥` (for `U` in the interval `[A,B]`) is equivalent, under `intervalEquiv`,
to the corresponding quotient submodule being disjoint from the image of `L`.  Uses
`A ⊓ L = ⊥`. -/
theorem intervalEquiv_inf_bot
    (A B L : Submodule K V) (hAB : A ≤ B) (hAL : A ⊓ L = ⊥)
    (U : {U : Submodule K V // A ≤ U ∧ U ≤ B}) :
    U.1 ⊓ L = ⊥ ↔
      (intervalEquiv A B hAB U) ⊓ Submodule.comap (Submodule.map A.mkQ B).subtype
        (Submodule.map A.mkQ L) = ⊥ := by
  set B' := Submodule.map A.mkQ B with hB'
  set D := Submodule.comap B'.subtype (Submodule.map A.mkQ L) with hD
  have hIE : (intervalEquiv A B hAB U)
      = Submodule.comap B'.subtype (Submodule.map A.mkQ U.1) := by
    rw [intervalEquiv]; rfl
  constructor
  · intro hU
    rw [eq_bot_iff]
    intro y hy
    rw [Submodule.mem_inf] at hy
    obtain ⟨hy1, hy2⟩ := hy
    have h1 : B'.subtype y ∈ Submodule.map A.mkQ U.1 := Submodule.mem_comap.mp hy1
    have h2 : B'.subtype y ∈ Submodule.map A.mkQ L := Submodule.mem_comap.mp hy2
    rw [Submodule.mem_map] at h1 h2
    obtain ⟨u, huU, hu_eq⟩ := h1
    obtain ⟨l, hlL, hl_eq⟩ := h2
    have hdiff : (u - l) ∈ A.mkQ.ker := by
      rw [LinearMap.mem_ker, map_sub, hu_eq, hl_eq, sub_self]
    rw [Submodule.ker_mkQ] at hdiff
    have hlU : l ∈ U.1 := by
      have : l = u - (u - l) := by abel
      rw [this]; exact U.1.sub_mem huU (U.2.1 hdiff)
    have hlbot : l ∈ (⊥ : Submodule K V) := by rw [← hU]; exact ⟨hlU, hlL⟩
    rw [Submodule.mem_bot] at hlbot
    rw [Submodule.mem_bot]
    apply Subtype.ext
    show B'.subtype y = 0
    rw [← hl_eq, hlbot, map_zero]
  · intro h
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_inf] at hx
    obtain ⟨hxU, hxL⟩ := hx
    have hmem : (⟨A.mkQ x, Submodule.mem_map_of_mem (f := A.mkQ) (U.2.2 hxU)⟩ : ↥B')
        ∈ (intervalEquiv A B hAB U) ⊓ D := by
      refine ⟨?_, ?_⟩
      · rw [hIE]
        show B'.subtype (⟨A.mkQ x, Submodule.mem_map_of_mem (f := A.mkQ) (U.2.2 hxU)⟩ : ↥B')
          ∈ Submodule.map A.mkQ U.1
        exact Submodule.mem_map_of_mem hxU
      · show A.mkQ x ∈ Submodule.map A.mkQ L
        exact Submodule.mem_map_of_mem hxL
    rw [h] at hmem
    rw [Submodule.mem_bot] at hmem
    have hzero : A.mkQ x = 0 := by
      have hv := congrArg Subtype.val hmem
      simpa using hv
    have hxA : x ∈ A := by rw [← Submodule.ker_mkQ A]; exact LinearMap.mem_ker.mpr hzero
    have : x ∈ (⊥ : Submodule K V) := by rw [← hAL]; exact ⟨hxA, hxL⟩
    rw [Submodule.mem_bot] at this
    exact this

section Quarter

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

/-- The `ℓ`-subspaces of `V` lying in `[A,B]` (counted by `finrank = ℓ`) correspond under
`intervalEquiv` to the `(ℓ - finrank A)`-subspaces of `B ⧸ A`. -/
noncomputable def allEquiv (A B : Submodule (ZMod 2) V) (hAB : A ≤ B) (ℓ : ℕ)
    (hAfin : Module.finrank (ZMod 2) A ≤ ℓ) :
    {U : Submodule (ZMod 2) V //
        Module.finrank (ZMod 2) U = ℓ ∧ A ≤ U ∧ U ≤ B} ≃
      {W : Submodule (ZMod 2) ↥(Submodule.map A.mkQ B) //
        Module.finrank (ZMod 2) W = ℓ - Module.finrank (ZMod 2) A} :=
  (Equiv.subtypeEquivRight (p := fun U : Submodule (ZMod 2) V =>
        Module.finrank (ZMod 2) U = ℓ ∧ A ≤ U ∧ U ≤ B)
      (q := fun U : Submodule (ZMod 2) V =>
        (A ≤ U ∧ U ≤ B) ∧ Module.finrank (ZMod 2) U = ℓ)
      (fun U => by tauto)).trans <|
    (Equiv.subtypeSubtypeEquivSubtypeInter (p := fun U : Submodule (ZMod 2) V => A ≤ U ∧ U ≤ B)
      (q := fun U : Submodule (ZMod 2) V => Module.finrank (ZMod 2) U = ℓ)).symm |>.trans <|
    Equiv.subtypeEquiv (intervalEquiv A B hAB) (fun U => by
      have hfle := intervalEquiv_finrank A B hAB U
      have hUle : Module.finrank (ZMod 2) A ≤ Module.finrank (ZMod 2) U.1 :=
        Submodule.finrank_mono U.2.1
      rw [hfle]; constructor <;> intro h <;> omega)

/-- Same correspondence for the "good" subspaces, additionally disjoint from `L`. -/
noncomputable def goodEquiv (A B L : Submodule (ZMod 2) V) (hAB : A ≤ B) (hAL : A ⊓ L = ⊥)
    (ℓ : ℕ) (hAfin : Module.finrank (ZMod 2) A ≤ ℓ) :
    {U : Submodule (ZMod 2) V //
        Module.finrank (ZMod 2) U = ℓ ∧ A ≤ U ∧ U ≤ B ∧ U ⊓ L = ⊥} ≃
      {W : Submodule (ZMod 2) ↥(Submodule.map A.mkQ B) //
        Module.finrank (ZMod 2) W = ℓ - Module.finrank (ZMod 2) A ∧
        W ⊓ (Submodule.comap (Submodule.map A.mkQ B).subtype (Submodule.map A.mkQ L)) = ⊥} :=
  (Equiv.subtypeEquivRight (p := fun U : Submodule (ZMod 2) V =>
        Module.finrank (ZMod 2) U = ℓ ∧ A ≤ U ∧ U ≤ B ∧ U ⊓ L = ⊥)
      (q := fun U : Submodule (ZMod 2) V =>
        (A ≤ U ∧ U ≤ B) ∧ (Module.finrank (ZMod 2) U = ℓ ∧ U ⊓ L = ⊥))
      (fun U => by tauto)).trans <|
    (Equiv.subtypeSubtypeEquivSubtypeInter (p := fun U : Submodule (ZMod 2) V => A ≤ U ∧ U ≤ B)
      (q := fun U : Submodule (ZMod 2) V =>
        Module.finrank (ZMod 2) U = ℓ ∧ U ⊓ L = ⊥)).symm |>.trans <|
    Equiv.subtypeEquiv (intervalEquiv A B hAB) (fun U => by
      have hfle := intervalEquiv_finrank A B hAB U
      have hbot := intervalEquiv_inf_bot A B L hAB hAL U
      have hUle : Module.finrank (ZMod 2) A ≤ Module.finrank (ZMod 2) U.1 :=
        Submodule.finrank_mono U.2.1
      rw [hbot]
      constructor
      · rintro ⟨hf, hb⟩
        exact ⟨by rw [hfle]; omega, hb⟩
      · rintro ⟨hf, hb⟩
        exact ⟨by rw [hfle] at hf; omega, hb⟩)

/-- **Core reduction.**  Over `𝔽₂`, for subspaces `A ≤ B` and any `L` with `A ⊓ L = ⊥`,
if the interval `[A,B]` contains an `ℓ`-subspace disjoint from `L`, then at least a quarter
of the `ℓ`-subspaces of `[A,B]` are disjoint from `L`.

Proof: quotient `V` by `A`; the interval `[A,B]` becomes `B ⧸ A`, the condition
`U ⊓ L = ⊥` becomes disjointness from the image of `L`, and the statement becomes
`Commons.LinearAlgebra.Submodule.card_inf_bot_ge_quarter` for the ambient space `B ⧸ A`.
The hypothesis `m + d ≤ finrank` of that lemma is supplied by the existence of the good
subspace (an explicit complement of `D`). -/
theorem card_interval_inf_bot_ge_quarter
    (A B L : Submodule (ZMod 2) V) (hAB : A ≤ B) (ℓ : ℕ)
    (hne : ∃ U : Submodule (ZMod 2) V,
      Module.finrank (ZMod 2) U = ℓ ∧ A ≤ U ∧ U ≤ B ∧ U ⊓ L = ⊥) :
    4 * Nat.card {U : Submodule (ZMod 2) V //
        Module.finrank (ZMod 2) U = ℓ ∧ A ≤ U ∧ U ≤ B ∧ U ⊓ L = ⊥}
      ≥ Nat.card {U : Submodule (ZMod 2) V //
        Module.finrank (ZMod 2) U = ℓ ∧ A ≤ U ∧ U ≤ B} := by
  classical
  obtain ⟨U₀, hU₀fin, hAU₀, hU₀B, hU₀L⟩ := hne
  have hAL : A ⊓ L = ⊥ :=
    le_bot_iff.mp ((inf_le_inf hAU₀ le_rfl).trans_eq hU₀L)
  have hAfin : Module.finrank (ZMod 2) A ≤ ℓ := by
    rw [← hU₀fin]; exact Submodule.finrank_mono hAU₀
  set B' := Submodule.map A.mkQ B with hB'
  set D : Submodule (ZMod 2) ↥B' :=
    Submodule.comap B'.subtype (Submodule.map A.mkQ L) with hD
  rw [Nat.card_congr (allEquiv A B hAB ℓ hAfin),
      Nat.card_congr (goodEquiv A B L hAB hAL ℓ hAfin)]
  refine card_inf_bot_ge_quarter (V := ↥B') (ℓ - Module.finrank (ZMod 2) A)
    (Module.finrank (ZMod 2) D) D rfl ?_
  set W₀ : Submodule (ZMod 2) ↥B' := intervalEquiv A B hAB ⟨U₀, hAU₀, hU₀B⟩ with hW₀
  have hW₀fin : Module.finrank (ZMod 2) W₀ = ℓ - Module.finrank (ZMod 2) A := by
    rw [hW₀, intervalEquiv_finrank]
    simp only [Subtype.coe_mk, hU₀fin]
  have hW₀bot : W₀ ⊓ D = ⊥ := by
    have h := (intervalEquiv_inf_bot A B L hAB hAL ⟨U₀, hAU₀, hU₀B⟩).mp hU₀L
    simpa [hW₀, hD, hB'] using h
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq W₀ D
  rw [hW₀bot, finrank_bot, add_zero, hW₀fin] at hsup
  have hle := Submodule.finrank_mono (le_top : W₀ ⊔ D ≤ ⊤)
  rw [finrank_top] at hle
  omega

end Quarter

/-- **Main statement.**  Let `K ≤ 𝔽₂ᵏ` have dimension `k - ℓ` and let `A ≤ B`.  If the
interval `[A,B]` of the Grassmannian contains an `ℓ`-subspace meeting `K` trivially, then
at least a quarter of the `ℓ`-subspaces of `[A,B]` meet `K` trivially. -/
theorem card_cell_good_ge_quarter {k ℓ : ℕ} (K A B : Submodule (ZMod 2) (Fin k → ZMod 2))
    (hK : Module.finrank (ZMod 2) K = k - ℓ) (hA : A ≤ B)
    (hne : ∃ U : Submodule (ZMod 2) (Fin k → ZMod 2),
      Module.finrank (ZMod 2) U = ℓ ∧ A ≤ U ∧ U ≤ B ∧ U ⊓ K = ⊥) :
    4 * Nat.card {U : Submodule (ZMod 2) (Fin k → ZMod 2) //
        Module.finrank (ZMod 2) U = ℓ ∧ A ≤ U ∧ U ≤ B ∧ U ⊓ K = ⊥}
      ≥ Nat.card {U : Submodule (ZMod 2) (Fin k → ZMod 2) //
        Module.finrank (ZMod 2) U = ℓ ∧ A ≤ U ∧ U ≤ B} :=
  card_interval_inf_bot_ge_quarter A B K hA ℓ hne

end Commons.LinearAlgebra.Submodule
