import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.TotallySplit
import Submission.Commons.LinearAlgebra.Submodule.card_submodule_finrank_inf_eq
import Submission.Commons.LinearAlgebra.Submodule.finrank_map_mkQ_of_le
import Submission.Commons.LinearAlgebra.Submodule.card_submodule_finrank_one_zmod_two
import Submission.Commons.LinearAlgebra.Submodule.card_submodule_le_finrank_eq

namespace Commons.LinearAlgebra.Submodule

open Module
set_option autoImplicit false

/-! ## General complement facts -/

section General

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Passing to the quotient `V ⧸ P` (with `P ⊓ L = ⊥`) turns complements of `L` into
complements of the image of `L`. -/
lemma isCompl_comap_mkQ_iff (P L : Submodule K V) (hPL : P ⊓ L = ⊥)
    (C : Submodule K (V ⧸ P)) :
    IsCompl (Submodule.comap P.mkQ C) L ↔ IsCompl C (Submodule.map P.mkQ L) := by
  rw [isCompl_iff, isCompl_iff, disjoint_iff, codisjoint_iff, disjoint_iff, codisjoint_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [eq_bot_iff]
      intro y hy
      rw [Submodule.mem_inf] at hy
      obtain ⟨hyC, hyL⟩ := hy
      rw [Submodule.mem_map] at hyL
      obtain ⟨l, hlL, rfl⟩ := hyL
      have hl : l ∈ Submodule.comap P.mkQ C := by rwa [Submodule.mem_comap]
      have h2' : l ∈ (⊥ : Submodule K V) := by
        have : l ∈ Submodule.comap P.mkQ C ⊓ L := ⟨hl, hlL⟩
        rwa [h1] at this
      rw [Submodule.mem_bot] at h2'
      rw [h2']
      simp
    · rw [eq_top_iff]
      intro y _
      obtain ⟨v, rfl⟩ := P.mkQ_surjective y
      have hv : v ∈ Submodule.comap P.mkQ C ⊔ L := by rw [h2]; trivial
      rw [Submodule.mem_sup] at hv
      obtain ⟨d, hd, l, hl, rfl⟩ := hv
      rw [map_add]
      refine Submodule.add_mem_sup ?_ (Submodule.mem_map_of_mem hl)
      rwa [Submodule.mem_comap] at hd
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [eq_bot_iff]
      intro v hv
      rw [Submodule.mem_inf] at hv
      obtain ⟨hvC, hvL⟩ := hv
      have hmem : P.mkQ v ∈ C ⊓ Submodule.map P.mkQ L :=
        ⟨by rwa [Submodule.mem_comap] at hvC, Submodule.mem_map_of_mem hvL⟩
      rw [h1] at hmem
      rw [Submodule.mem_bot] at hmem
      have hvP : v ∈ P := by
        rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hmem
      have : v ∈ (⊥ : Submodule K V) := by
        have : v ∈ P ⊓ L := ⟨hvP, hvL⟩
        rwa [hPL] at this
      simpa using this
    · rw [eq_top_iff]
      intro v _
      have hv : P.mkQ v ∈ C ⊔ Submodule.map P.mkQ L := by rw [h2]; trivial
      rw [Submodule.mem_sup] at hv
      obtain ⟨y, hyC, z, hzL, hyz⟩ := hv
      obtain ⟨c, rfl⟩ := P.mkQ_surjective y
      rw [Submodule.mem_map] at hzL
      obtain ⟨l, hlL, rfl⟩ := hzL
      have hc : c ∈ Submodule.comap P.mkQ C := by rwa [Submodule.mem_comap]
      have hkey : v - (c + l) ∈ P := by
        rw [← Submodule.ker_mkQ P]
        show P.mkQ (v - (c + l)) = 0
        rw [map_sub, map_add, hyz, sub_self]
      have hpl : v - (c + l) ∈ Submodule.comap P.mkQ C :=
        (Submodule.le_comap_mkQ P C) hkey
      rw [show v = (v - (c + l)) + (c + l) from by abel]
      exact add_mem (Submodule.mem_sup_left hpl)
        (Submodule.add_mem_sup hc hlL)

/-- Complements of `L` containing `P` correspond to complements of `L/P` in `V/P`. -/
noncomputable def complContainingEquiv (P L : Submodule K V) (hPL : P ⊓ L = ⊥) :
    {D : Submodule K V // IsCompl D L ∧ P ≤ D} ≃
      {C : Submodule K (V ⧸ P) // IsCompl C (Submodule.map P.mkQ L)} where
  toFun D := ⟨Submodule.map P.mkQ D.1, (isCompl_comap_mkQ_iff P L hPL _).mp (by
      have hc : Submodule.comap P.mkQ (Submodule.map P.mkQ D.1) = D.1 := by
        rw [Submodule.comap_map_mkQ, sup_eq_right.mpr D.2.2]
      rw [hc]; exact D.2.1)⟩
  invFun C := ⟨Submodule.comap P.mkQ C.1, (isCompl_comap_mkQ_iff P L hPL C.1).mpr C.2,
      Submodule.le_comap_mkQ P C.1⟩
  left_inv D := by
    apply Subtype.ext
    change Submodule.comap P.mkQ (Submodule.map P.mkQ D.1) = D.1
    rw [Submodule.comap_map_mkQ, sup_eq_right.mpr D.2.2]
  right_inv C := by
    apply Subtype.ext
    exact Submodule.map_comap_eq_self (by rw [Submodule.range_mkQ]; exact le_top)

/-- The number of complements of `L` (in the finite space `V`) that contain a fixed
complementary subspace `P`. -/
lemma card_isCompl_containing [Fintype K] [Module.Finite K V] (P L : Submodule K V)
    (hPL : P ⊓ L = ⊥) :
    Nat.card {D : Submodule K V // IsCompl D L ∧ P ≤ D}
      = (Nat.card K) ^ ((Module.finrank K V - Module.finrank K P - Module.finrank K L) *
          Module.finrank K L) := by
  rw [Nat.card_congr (complContainingEquiv P L hPL)]
  rw [card_isCompl (Submodule.map P.mkQ L)]
  congr 1
  have h1 : Module.finrank K (V ⧸ P) = Module.finrank K V - Module.finrank K P :=
    Submodule.finrank_quotient P
  have h2 : Module.finrank K ↥(Submodule.map P.mkQ L) = Module.finrank K L := by
    have h := finrank_map_mkQ_add_finrank_inf P L
    rw [hPL, finrank_bot K V] at h
    omega
  rw [h1, h2]

/-- `Nat.card` of a subtype of a finite type as the size of a filtered `Finset.univ`. -/
lemma natCard_subtype_eq_card_filter {α : Type*} [Fintype α] (p : α → Prop)
    [DecidablePred p] :
    Nat.card {x : α // p x} = (Finset.univ.filter p).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

end General

/-! ## The counting ingredients -/

section Counting

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma isCompl_iff_finrank_inf_eq_bot [Module.Finite K V] (D L : Submodule K V) :
    IsCompl D L ↔
      Module.finrank K D = Module.finrank K V - Module.finrank K L ∧ D ⊓ L = ⊥ := by
  have hle : Module.finrank K L ≤ Module.finrank K V :=
    (by simpa using Submodule.finrank_mono (le_top : L ≤ ⊤) : Module.finrank K L ≤ Module.finrank K V)
  constructor
  · intro h
    have hd : D ⊓ L = ⊥ := disjoint_iff.mp h.disjoint
    refine ⟨?_, hd⟩
    have hfr := Submodule.finrank_sup_add_finrank_inf_eq D L
    rw [h.codisjoint.eq_top, finrank_top, hd, finrank_bot K V] at hfr
    omega
  · rintro ⟨hfr, hdisj⟩
    refine (isCompl_iff).mpr ⟨by rwa [disjoint_iff], ?_⟩
    rw [codisjoint_iff, Submodule.eq_top_iff_finrank_eq]
    have hfr2 := Submodule.finrank_sup_add_finrank_inf_eq D L
    rw [hdisj, finrank_bot K V] at hfr2
    omega

lemma card_inf_eq_bot_eq_pow [Fintype K] [Module.Finite K V] (L : Submodule K V) :
    Nat.card {D : Submodule K V //
        Module.finrank K D = Module.finrank K V - Module.finrank K L ∧ D ⊓ L = ⊥}
      = (Nat.card K) ^ ((Module.finrank K V - Module.finrank K L) * Module.finrank K L) := by
  rw [← Nat.card_congr (Equiv.subtypeEquivRight (fun D => isCompl_iff_finrank_inf_eq_bot D L))]
  exact card_isCompl L

lemma card_inf_eq_bot_containing [Fintype K] [Module.Finite K V] (P L : Submodule K V)
    (hPL : P ⊓ L = ⊥) :
    Nat.card {D : Submodule K V //
        Module.finrank K D = Module.finrank K V - Module.finrank K L ∧ D ⊓ L = ⊥ ∧ P ≤ D}
      = (Nat.card K) ^ ((Module.finrank K V - Module.finrank K P - Module.finrank K L) *
          Module.finrank K L) := by
  have hiff : ∀ D : Submodule K V,
      (Module.finrank K D = Module.finrank K V - Module.finrank K L ∧ D ⊓ L = ⊥ ∧ P ≤ D)
        ↔ (IsCompl D L ∧ P ≤ D) := by
    intro D
    constructor
    · rintro ⟨hf, hfl, hPD⟩
      exact ⟨(isCompl_iff_finrank_inf_eq_bot D L).mpr ⟨hf, hfl⟩, hPD⟩
    · rintro ⟨hcomp, hPD⟩
      obtain ⟨hf, hfl⟩ := (isCompl_iff_finrank_inf_eq_bot D L).mp hcomp
      exact ⟨hf, hfl, hPD⟩
  rw [Nat.card_congr (Equiv.subtypeEquivRight hiff)]
  exact card_isCompl_containing P L hPL

lemma le_of_finrank_eq_one_of_inf_ne_bot [Module.Finite K V] {P L : Submodule K V}
    (hP : Module.finrank K P = 1) (h : P ⊓ L ≠ ⊥) : P ≤ L := by
  have hle : P ⊓ L ≤ P := inf_le_left
  have hpos : Module.finrank K ↥(P ⊓ L) ≠ 0 := by
    intro h0
    exact h ((Submodule.finrank_eq_zero).mp h0)
  have hle1 : Module.finrank K ↥(P ⊓ L) ≤ 1 := by
    rw [← hP]; exact Submodule.finrank_mono hle
  have hfin : Module.finrank K ↥(P ⊓ L) = Module.finrank K P := by omega
  rw [← Submodule.eq_of_le_of_finrank_eq hle hfin]
  exact inf_le_right

lemma inf_eq_bot_iff_not_le_of_finrank_one [Module.Finite K V] {P L : Submodule K V}
    (hP : Module.finrank K P = 1) : P ⊓ L = ⊥ ↔ ¬ P ≤ L := by
  constructor
  · intro h hle
    have hb : P ≤ (⊥ : Submodule K V) := by rw [← h]; exact le_inf le_rfl hle
    have hPeq : P = ⊥ := le_bot_iff.mp hb
    have : Module.finrank K P = 0 := by rw [hPeq, finrank_bot K V]
    omega
  · intro h
    by_contra hne
    exact h (le_of_finrank_eq_one_of_inf_ne_bot hP hne)

/-- If `D` is disjoint from `L` and `L ⊓ L'` is a hyperplane of `L'`, then `D` meets `L'` in
at most a line. -/
lemma finrank_inf_le_one [Module.Finite K V] (D L L' : Submodule K V) (hDL : D ⊓ L = ⊥)
    (hLL' : Module.finrank K ↥(L ⊓ L') + 1 = Module.finrank K L') :
    Module.finrank K ↥(D ⊓ L') ≤ 1 := by
  have hdm : D ⊓ (L ⊓ L') = ⊥ := by rw [← inf_assoc, hDL, bot_inf_eq]
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq D (L ⊓ L')
  rw [hdm, finrank_bot K V] at h1
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq D L'
  have h3 : Module.finrank K ↥(D ⊔ (L ⊓ L')) ≤ Module.finrank K ↥(D ⊔ L') :=
    Submodule.finrank_mono (sup_le_sup_left inf_le_right D)
  omega

lemma fiber_inf_eq_of_le [Module.Finite K V] (L L' P : Submodule K V) (m : ℕ)
    (hP : Module.finrank K P = 1)
    (hPL' : P ≤ L') (hPL : P ⊓ L = ⊥)
    (hone : ∀ D : Submodule K V, D ⊓ L = ⊥ → Module.finrank K ↥(D ⊓ L') ≤ 1) :
    ∀ D : Submodule K V,
      (Module.finrank K D = m ∧ D ⊓ L = ⊥ ∧ D ⊓ L' ≠ ⊥ ∧ D ⊓ L' = P)
        ↔ (Module.finrank K D = m ∧ D ⊓ L = ⊥ ∧ P ≤ D) := by
  intro D
  constructor
  · rintro ⟨hf, hfl, _, hfiber⟩
    exact ⟨hf, hfl, hfiber ▸ inf_le_left⟩
  · rintro ⟨hf, hfl, hPD⟩
    have hle : P ≤ D ⊓ L' := le_inf hPD hPL'
    have hfin : Module.finrank K ↥(D ⊓ L') = Module.finrank K P := by
      apply le_antisymm
      · have := hone D hfl; omega
      · exact Submodule.finrank_mono hle
    have heq : P = D ⊓ L' := Submodule.eq_of_le_of_finrank_eq hle hfin.symm
    have hne : D ⊓ L' ≠ ⊥ := by
      rw [← heq]
      intro hbot
      have : Module.finrank K P = 0 := by rw [hbot, finrank_bot K V]
      omega
    exact ⟨hf, hfl, hne, heq.symm⟩


end Counting

section Lines

lemma card_lines_not_le {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (L L' : Submodule (ZMod 2) V)
    (h : Module.finrank (ZMod 2) ↥(L ⊓ L') + 1 = Module.finrank (ZMod 2) L') :
    Nat.card {P : Submodule (ZMod 2) V //
        Module.finrank (ZMod 2) P = 1 ∧ P ≤ L' ∧ P ⊓ L = ⊥}
      = 2 ^ (Module.finrank (ZMod 2) L' - 1) := by
  classical
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  set T1 := Finset.univ.filter (fun P : Submodule (ZMod 2) V =>
      Module.finrank (ZMod 2) P = 1 ∧ P ≤ L') with hT1
  set T2 := Finset.univ.filter (fun P : Submodule (ZMod 2) V =>
      Module.finrank (ZMod 2) P = 1 ∧ P ≤ L' ∧ P ⊓ L = ⊥) with hT2
  set T0 := Finset.univ.filter (fun P : Submodule (ZMod 2) V =>
      Module.finrank (ZMod 2) P = 1 ∧ P ≤ L ⊓ L') with hT0
  have hT2eq : T2 = T1.filter (fun P => P ⊓ L = ⊥) := by
    rw [hT1, hT2]; apply Finset.ext; intro P
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have hT0eq : T0 = T1.filter (fun P => ¬ (P ⊓ L = ⊥)) := by
    rw [hT1, hT0]; apply Finset.ext; intro P
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hf, hle⟩
      refine ⟨⟨hf, le_trans hle inf_le_right⟩, ?_⟩
      intro hbot
      exact (inf_eq_bot_iff_not_le_of_finrank_one hf).mp hbot (le_trans hle inf_le_left)
    · rintro ⟨⟨hf, hleL'⟩, hnot⟩
      exact ⟨hf, le_inf (le_of_finrank_eq_one_of_inf_ne_bot hf hnot) hleL'⟩
  have hsplit : T1.card = T2.card + T0.card := by
    rw [hT2eq, hT0eq]
    exact (Finset.card_filter_add_card_filter_not (fun P => P ⊓ L = ⊥) (s := T1)).symm
  have hT1c : T1.card = 2 ^ Module.finrank (ZMod 2) L' - 1 := by
    rw [← natCard_subtype_eq_card_filter (fun P : Submodule (ZMod 2) V =>
      Module.finrank (ZMod 2) P = 1 ∧ P ≤ L')]
    have hswap : ∀ P : Submodule (ZMod 2) V,
        (Module.finrank (ZMod 2) P = 1 ∧ P ≤ L') ↔ (P ≤ L' ∧ Module.finrank (ZMod 2) P = 1) :=
      fun P => ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
    rw [Nat.card_congr (Equiv.subtypeEquivRight hswap)]
    rw [card_submodule_le_finrank_eq L' 1]
    exact card_submodule_finrank_one_zmod_two
  have hT0c : T0.card = 2 ^ Module.finrank (ZMod 2) ↥(L ⊓ L') - 1 := by
    rw [← natCard_subtype_eq_card_filter (fun P : Submodule (ZMod 2) V =>
      Module.finrank (ZMod 2) P = 1 ∧ P ≤ L ⊓ L')]
    have hswap : ∀ P : Submodule (ZMod 2) V,
        (Module.finrank (ZMod 2) P = 1 ∧ P ≤ L ⊓ L') ↔
          (P ≤ L ⊓ L' ∧ Module.finrank (ZMod 2) P = 1) :=
      fun P => ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
    rw [Nat.card_congr (Equiv.subtypeEquivRight hswap)]
    rw [card_submodule_le_finrank_eq (L ⊓ L') 1]
    exact card_submodule_finrank_one_zmod_two
  have hge : 1 ≤ Module.finrank (ZMod 2) L' := by omega
  have hn' : Module.finrank (ZMod 2) ↥(L ⊓ L') = Module.finrank (ZMod 2) L' - 1 := by omega
  have hb : 2 ^ Module.finrank (ZMod 2) L' =
      2 ^ (Module.finrank (ZMod 2) L' - 1) * 2 := by
    calc 2 ^ Module.finrank (ZMod 2) L'
        = 2 ^ ((Module.finrank (ZMod 2) L' - 1) + 1) := by
          congr 1
          omega
      _ = 2 ^ (Module.finrank (ZMod 2) L' - 1) * 2 := by rw [pow_succ]
  have hT2c : T2.card = 2 ^ (Module.finrank (ZMod 2) L' - 1) := by
    have hh := hsplit
    rw [hT1c, hT0c, hn'] at hh
    omega
  rw [natCard_subtype_eq_card_filter (fun P : Submodule (ZMod 2) V =>
      Module.finrank (ZMod 2) P = 1 ∧ P ≤ L' ∧ P ⊓ L = ⊥), ← hT2]
  exact hT2c


end Lines

section Main

/-- **Half of the transversals of `L` also meet `L'` trivially.**
Let `L, L'` be `ℓ`-dimensional subspaces of `𝔽₂^k` with `dim (L ⊓ L') = ℓ - 1` (adjacent
vertices of the Grassmann graph).  Then exactly half of the `(k-ℓ)`-dimensional subspaces `D`
with `D ⊓ L = ⊥` also satisfy `D ⊓ L' = ⊥`. -/
theorem card_inf_bot_pairs (k ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hℓk : ℓ ≤ k)
    (L L' : Submodule (ZMod 2) (Fin k → ZMod 2))
    (hL : Module.finrank (ZMod 2) L = ℓ) (hL' : Module.finrank (ZMod 2) L' = ℓ)
    (hadj : Module.finrank (ZMod 2) ↥(L ⊓ L') = ℓ - 1) :
    2 * Nat.card {D : Submodule (ZMod 2) (Fin k → ZMod 2) //
        Module.finrank (ZMod 2) D = k - ℓ ∧ D ⊓ L = ⊥ ∧ D ⊓ L' = ⊥}
      = Nat.card {D : Submodule (ZMod 2) (Fin k → ZMod 2) //
        Module.finrank (ZMod 2) D = k - ℓ ∧ D ⊓ L = ⊥}
:= by
  classical
  have hE : Module.finrank (ZMod 2) (Fin k → ZMod 2) = k := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hL'ne : L' ≠ ⊤ := by
    intro htop
    have h1 : Module.finrank (ZMod 2) ↥(L ⊓ L') = ℓ := by rw [htop, inf_top_eq, hL]
    rw [hadj] at h1
    omega
  have hℓ_lt : ℓ < k := by
    have h := Submodule.finrank_lt hL'ne
    rw [hL', hE] at h
    exact h
  have hLL' : Module.finrank (ZMod 2) ↥(L ⊓ L') + 1 = Module.finrank (ZMod 2) L' := by
    rw [hadj, hL']; omega
  have hk1 : k - 1 - ℓ = k - ℓ - 1 := by omega
  have hkm : 1 ≤ k - ℓ := by omega
  have hP1 : 1 ≤ ℓ * (k - ℓ) := Nat.mul_pos (by omega) (by omega)
  set Afin := Finset.univ.filter (fun D : Submodule (ZMod 2) (Fin k → ZMod 2) =>
      Module.finrank (ZMod 2) D = k - ℓ ∧ D ⊓ L = ⊥) with hAfin
  set Bfin := Finset.univ.filter (fun D : Submodule (ZMod 2) (Fin k → ZMod 2) =>
      Module.finrank (ZMod 2) D = k - ℓ ∧ D ⊓ L = ⊥ ∧ D ⊓ L' = ⊥) with hBfin
  set Cfin := Finset.univ.filter (fun D : Submodule (ZMod 2) (Fin k → ZMod 2) =>
      Module.finrank (ZMod 2) D = k - ℓ ∧ D ⊓ L = ⊥ ∧ D ⊓ L' ≠ ⊥) with hCfin
  set Pset := Finset.univ.filter (fun P : Submodule (ZMod 2) (Fin k → ZMod 2) =>
      Module.finrank (ZMod 2) P = 1 ∧ P ≤ L' ∧ P ⊓ L = ⊥) with hPset
  have hAn : Nat.card {D : Submodule (ZMod 2) (Fin k → ZMod 2) //
      Module.finrank (ZMod 2) D = k - ℓ ∧ D ⊓ L = ⊥} = Afin.card := by
    rw [hAfin]
    exact natCard_subtype_eq_card_filter (fun D : Submodule (ZMod 2) (Fin k → ZMod 2) =>
      Module.finrank (ZMod 2) D = k - ℓ ∧ D ⊓ L = ⊥)
  have hBn : Nat.card {D : Submodule (ZMod 2) (Fin k → ZMod 2) //
      Module.finrank (ZMod 2) D = k - ℓ ∧ D ⊓ L = ⊥ ∧ D ⊓ L' = ⊥} = Bfin.card := by
    rw [hBfin]
    exact natCard_subtype_eq_card_filter (fun D : Submodule (ZMod 2) (Fin k → ZMod 2) =>
      Module.finrank (ZMod 2) D = k - ℓ ∧ D ⊓ L = ⊥ ∧ D ⊓ L' = ⊥)
  -- The bad set splits as `A = B ⊔ C`.
  have hsplit : Afin.card = Bfin.card + Cfin.card := by
    have hfil1 : Afin.filter (fun D => D ⊓ L' = ⊥) = Bfin := by
      rw [hAfin, hBfin]; apply Finset.ext; intro D
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
    have hfil2 : Afin.filter (fun D => ¬ (D ⊓ L' = ⊥)) = Cfin := by
      rw [hAfin, hCfin]; apply Finset.ext; intro D
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
    have h := Finset.card_filter_add_card_filter_not
      (fun D : Submodule (ZMod 2) (Fin k → ZMod 2) => D ⊓ L' = ⊥) (s := Afin)
    rw [hfil1, hfil2] at h
    exact h.symm
  -- Cardinality of the good set.
  have hAcard : Afin.card = 2 ^ (ℓ * (k - ℓ)) := by
    rw [← hAn]
    have h := card_inf_eq_bot_eq_pow (K := ZMod 2) (V := Fin k → ZMod 2) L
    rw [hE, hL, Nat.card_zmod] at h
    rw [h, Nat.mul_comm (k - ℓ) ℓ]
  -- Cardinality of the set of lines.
  have hPsetcard : Pset.card = 2 ^ (ℓ - 1) := by
    rw [hPset, ← natCard_subtype_eq_card_filter
      (fun P : Submodule (ZMod 2) (Fin k → ZMod 2) =>
        Module.finrank (ZMod 2) P = 1 ∧ P ≤ L' ∧ P ⊓ L = ⊥)]
    rw [card_lines_not_le L L' hLL', hL']
  -- The map `D ↦ D ⊓ L'` sends the bad set into the lines.
  have hmaps : Set.MapsTo (fun D : Submodule (ZMod 2) (Fin k → ZMod 2) => D ⊓ L')
      ↑Cfin ↑Pset := by
    intro D hD
    simp only [Finset.mem_coe, hCfin, Finset.mem_filter, Finset.mem_univ, true_and] at hD
    obtain ⟨hfin, hDL, hne⟩ := hD
    simp only [Finset.mem_coe, hPset, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, inf_le_right, ?_⟩
    · have hle := finrank_inf_le_one D L L' hDL hLL'
      have hne0 : Module.finrank (ZMod 2) ↥(D ⊓ L') ≠ 0 := by
        intro h0
        exact hne ((Submodule.finrank_eq_zero).mp h0)
      omega
    · rw [inf_assoc, inf_comm L' L, ← inf_assoc, hDL, bot_inf_eq]
  have hdecomp := Finset.card_eq_sum_card_fiberwise hmaps
  -- Each fibre is the set of complements of `L` containing the line.
  have hfiber : ∀ P ∈ Pset, (Cfin.filter (fun D => D ⊓ L' = P)).card =
      2 ^ ((k - 1 - ℓ) * ℓ) := by
    intro P hP
    simp only [hPset, Finset.mem_filter, Finset.mem_univ, true_and] at hP
    obtain ⟨hPd, hPL', hPL⟩ := hP
    have hfib := fiber_inf_eq_of_le L L' P (k - ℓ) hPd hPL' hPL
      (fun D hDL => finrank_inf_le_one D L L' hDL hLL')
    have hfibereq : Cfin.filter (fun D => D ⊓ L' = P) =
        Finset.univ.filter (fun D : Submodule (ZMod 2) (Fin k → ZMod 2) =>
          Module.finrank (ZMod 2) D = k - ℓ ∧ D ⊓ L = ⊥ ∧ P ≤ D) := by
      rw [hCfin]
      apply Finset.ext
      intro D
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨hfin, hDL, hne⟩, hfeq⟩
        exact hfib D |>.mp ⟨hfin, hDL, hne, hfeq⟩
      · intro h
        obtain ⟨hfin, hDL, hne, hfeq⟩ := hfib D |>.mpr h
        exact ⟨⟨hfin, hDL, hne⟩, hfeq⟩
    rw [hfibereq, ← natCard_subtype_eq_card_filter
      (fun D : Submodule (ZMod 2) (Fin k → ZMod 2) =>
        Module.finrank (ZMod 2) D = k - ℓ ∧ D ⊓ L = ⊥ ∧ P ≤ D)]
    have hc := card_inf_eq_bot_containing (K := ZMod 2) (V := Fin k → ZMod 2) P L hPL
    rw [hE, hL, hPd, Nat.card_zmod] at hc
    exact hc
  -- Cardinality of the bad set.
  have hCcard : Cfin.card = 2 ^ (ℓ * (k - ℓ) - 1) := by
    rw [hdecomp, Finset.sum_congr rfl hfiber, Finset.sum_const, smul_eq_mul, hPsetcard]
    rw [← pow_add]
    congr 1
    have h1 : k - 1 - ℓ = k - ℓ - 1 := by omega
    have h2 : (k - ℓ - 1) * ℓ = ℓ * (k - ℓ) - ℓ := by
      rw [Nat.mul_sub_right_distrib, one_mul, Nat.mul_comm (k - ℓ) ℓ]
    rw [h1, h2]
    have hle : ℓ ≤ ℓ * (k - ℓ) := by
      calc ℓ = ℓ * 1 := (Nat.mul_one ℓ).symm
        _ ≤ ℓ * (k - ℓ) := Nat.mul_le_mul_left ℓ hkm
    omega
  have hBcard : Bfin.card = 2 ^ (ℓ * (k - ℓ) - 1) := by
    have h := hsplit
    rw [hAcard, hCcard] at h
    have hp : 2 ^ (ℓ * (k - ℓ)) = 2 ^ (ℓ * (k - ℓ) - 1) * 2 := by
      calc 2 ^ (ℓ * (k - ℓ)) = 2 ^ ((ℓ * (k - ℓ) - 1) + 1) := by congr 1; omega
        _ = 2 ^ (ℓ * (k - ℓ) - 1) * 2 := by rw [pow_succ]
    omega
  have htarget : 2 * Bfin.card = Afin.card := by
    rw [hBcard, hAcard]
    calc 2 * 2 ^ (ℓ * (k - ℓ) - 1) = 2 ^ (ℓ * (k - ℓ) - 1) * 2 := by ring
      _ = 2 ^ ((ℓ * (k - ℓ) - 1) + 1) := by rw [pow_succ]
      _ = 2 ^ (ℓ * (k - ℓ)) := by congr 1; omega
  rw [hAn, hBn]
  exact htarget

end Main

end Commons.LinearAlgebra.Submodule