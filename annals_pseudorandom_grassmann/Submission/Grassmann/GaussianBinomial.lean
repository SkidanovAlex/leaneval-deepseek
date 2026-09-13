import Mathlib
import Submission.Grassmann.Counting
import Submission.Commons.LinearAlgebra.Submodule.card_submodule_finrank_eq_of_finrank_eq

/-!
# Enumeration of the Grassmannian over `𝔽₂`: the Gaussian binomial `[n choose m]_2`

This file completes the *quantitative* layer of the counting theory: the number of
`m`-dimensional subspaces of `𝔽₂ⁿ`, written `grCount n m`, together with the classical
product formula (via double counting ordered linearly independent tuples) and two-sided
exponential bounds.  It also identifies the interval counts `#(SubGr k ℓ A B)` of
`Submission.Grassmann.Counting` with `grCount` values.

Main results:

* `linIndep_card`: the number of ordered linearly independent `m`-tuples in a finite
  `𝔽₂`-space `V` is `∏_{i<m} (#V - 2^i)`;
* `grCount_mul`: `grCount n m * ∏_{i<m}(2^m - 2^i) = ∏_{i<m}(2^n - 2^i)`;
* `grCount_lower` / `grCount_upper`: for `m ≤ n`,
  `2^{m(n-m)} ≤ grCount n m ≤ 2^{m(n-m)+m}`;
* `card_SubGr_eq_grCount`: for `A ≤ B` and `finrank A ≤ ℓ`,
  `#(SubGr k ℓ A B) = grCount (finrank B - finrank A) (ℓ - finrank A)`, with matching
  lower/upper bounds `card_SubGr_lower` / `card_SubGr_upper`.
-/

open PseudorandomGrassmann
open Module Submodule Finset Filter
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

local notation "𝔽₂" => ZMod 2

namespace Submission.Grassmann
namespace F2

section FiniteV

variable {V : Type*} [AddCommGroup V] [Module 𝔽₂ V] [Finite V]

/-- The complement of the span of a linearly independent `m`-tuple has
`#V - 2^m` elements. -/
lemma card_compl_span {m : ℕ} (s : Fin m → V) (hs : LinearIndependent 𝔽₂ s) :
    Nat.card {v : V // v ∉ Submodule.span 𝔽₂ (Set.range s)} = Nat.card V - 2 ^ m := by
  classical
  haveI : Fintype V := Fintype.ofFinite V
  haveI : Fintype {v : V // v ∈ Submodule.span 𝔽₂ (Set.range s)} :=
    Fintype.ofFinite {v : V // v ∈ Submodule.span 𝔽₂ (Set.range s)}
  haveI : Fintype {v : V // v ∉ Submodule.span 𝔽₂ (Set.range s)} :=
    Fintype.ofFinite {v : V // v ∉ Submodule.span 𝔽₂ (Set.range s)}
  have hfin : Module.finrank 𝔽₂ (Submodule.span 𝔽₂ (Set.range s)) = m := by
    rw [finrank_span_eq_card hs, Fintype.card_fin]
  have h2 : Nat.card ↥(Submodule.span 𝔽₂ (Set.range s)) = 2 ^ m := by
    rw [Module.natCard_eq_pow_finrank (K := 𝔽₂), Nat.card_zmod, hfin]
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_subtype_compl (fun v : V => v ∈ Submodule.span 𝔽₂ (Set.range s)),
    ← Nat.card_eq_fintype_card (α := V)]
  congr 1
  rw [← Nat.card_eq_fintype_card (α := {v : V // v ∈ Submodule.span 𝔽₂ (Set.range s)})]
  exact h2

/-- The number of ordered linearly independent `m`-tuples of vectors of a finite
`𝔽₂`-space `V` is `∏_{i<m} (#V - 2^i)`. -/
theorem linIndep_card (m : ℕ) :
    Nat.card {f : Fin m → V // LinearIndependent 𝔽₂ f} =
      ∏ i ∈ Finset.range m, (Nat.card V - 2 ^ i) := by
  classical
  haveI : Fintype V := Fintype.ofFinite V
  induction m with
  | zero =>
      rw [Finset.prod_range_zero]
      exact Nat.card_eq_one_iff_unique.mpr
        ⟨inferInstance, ⟨⟨Fin.elim0, linearIndependent_empty_type⟩⟩⟩
  | succ m ih =>
      rw [Finset.prod_range_succ, ← ih]
      refine (Nat.card_congr (equiv_linearIndependent (K := 𝔽₂) (V := V) m)).trans ?_
      calc Nat.card (Σ s : {f : Fin m → V // LinearIndependent 𝔽₂ f},
              ((↑(Submodule.span 𝔽₂ (Set.range (s : Fin m → V))))ᶜ : Set V))
          = ∑ s : {f : Fin m → V // LinearIndependent 𝔽₂ f},
              Nat.card ((↑(Submodule.span 𝔽₂ (Set.range (s : Fin m → V))))ᶜ : Set V) :=
            Nat.card_sigma
        _ = ∑ _s : {f : Fin m → V // LinearIndependent 𝔽₂ f}, (Nat.card V - 2 ^ m) :=
            Finset.sum_congr rfl (fun s _ => by
              obtain ⟨f, hf⟩ := s
              exact card_compl_span f hf)
        _ = Nat.card {f : Fin m → V // LinearIndependent 𝔽₂ f} * (Nat.card V - 2 ^ m) := by
            rw [Finset.sum_const, Finset.card_univ,
              ← Nat.card_eq_fintype_card (α := {f : Fin m → V // LinearIndependent 𝔽₂ f})]
            simp [smul_eq_mul]

/-- Coercing a linearly independent tuple in a submodule to the ambient space. -/
lemma linearIndependent_coe_subtype {m : ℕ} {W : Submodule 𝔽₂ V} {g : Fin m → ↥W}
    (hg : LinearIndependent 𝔽₂ g) : LinearIndependent 𝔽₂ (fun i => (g i : V)) :=
  hg.map' (Submodule.subtype W) (Submodule.ker_subtype W)

end FiniteV

section FintypeV

variable {V : Type*} [AddCommGroup V] [Module 𝔽₂ V] [Fintype V]

/-- Double counting independent tuples by their span. -/
theorem linIndep_eq_sum (m : ℕ) :
    Nat.card {f : Fin m → V // LinearIndependent 𝔽₂ f} =
      ∑ W : {W : Submodule 𝔽₂ V // Module.finrank 𝔽₂ W = m},
        Nat.card {f : Fin m → V // LinearIndependent 𝔽₂ f ∧
          Submodule.span 𝔽₂ (Set.range f) = W.1} := by
  classical
  rw [← Nat.card_sigma (β := fun W : {W : Submodule 𝔽₂ V // Module.finrank 𝔽₂ W = m} =>
        {f : Fin m → V // LinearIndependent 𝔽₂ f ∧
          Submodule.span 𝔽₂ (Set.range f) = W.1})]
  refine Nat.card_congr ?_
  refine
    { toFun := fun f => ⟨⟨Submodule.span 𝔽₂ (Set.range (f : Fin m → V)),
          by rw [finrank_span_eq_card f.2, Fintype.card_fin]⟩,
        ⟨(f : Fin m → V), f.2, rfl⟩⟩
      invFun := fun s => ⟨s.2.1, s.2.2.1⟩
      left_inv := fun f => rfl
      right_inv := fun s => ?_ }
  obtain ⟨⟨W, hW⟩, ⟨f, hf, hspan⟩⟩ := s
  refine Sigma.ext (Subtype.ext hspan) ?_
  rw [Subtype.heq_iff_coe_eq (fun x =>
    ⟨fun h => ⟨h.1, h.2.trans hspan⟩, fun h => ⟨h.1, h.2.trans hspan.symm⟩⟩)]

/-- The independent `m`-tuples whose span is `W` are the independent `m`-tuples in `↥W`. -/
noncomputable def spanFiberEquiv (m : ℕ) (W : Submodule 𝔽₂ V)
    (hW : Module.finrank 𝔽₂ W = m) :
    {f : Fin m → V // LinearIndependent 𝔽₂ f ∧
        Submodule.span 𝔽₂ (Set.range f) = W} ≃
      {g : Fin m → ↥W // LinearIndependent 𝔽₂ g} where
  toFun F :=
    ⟨fun i => ⟨F.1 i, by
        have h : F.1 i ∈ Submodule.span 𝔽₂ (Set.range F.1) := Submodule.subset_span ⟨i, rfl⟩
        rwa [F.2.2] at h⟩,
      LinearIndependent.of_comp (Submodule.subtype W) (by
        convert F.2.1 using 1
        funext i
        rfl)⟩
  invFun g :=
    ⟨fun i => ((g : Fin m → ↥W) i : V), linearIndependent_coe_subtype g.2, by
      have hle : Submodule.span 𝔽₂ (Set.range (fun i => ((g : Fin m → ↥W) i : V))) ≤ W := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact ((g : Fin m → ↥W) i).2
      have hdim : Module.finrank 𝔽₂
          ↥(Submodule.span 𝔽₂ (Set.range (fun i => ((g : Fin m → ↥W) i : V)))) =
          Module.finrank 𝔽₂ ↥W := by
        rw [finrank_span_eq_card (linearIndependent_coe_subtype g.2), hW, Fintype.card_fin]
      exact Submodule.eq_of_le_of_finrank_eq hle hdim⟩
  left_inv F := by
    apply Subtype.ext
    funext i
    rfl
  right_inv g := by
    apply Subtype.ext
    funext i
    exact Subtype.ext rfl

end FintypeV

/-! ## The Gaussian binomial -/

/-- The number of `m`-dimensional subspaces of `𝔽₂ⁿ`, i.e. the Gaussian binomial
`[n choose m]_2`. -/
noncomputable def grCount (n m : ℕ) : ℕ :=
  Nat.card {W : Submodule 𝔽₂ (Fin n → 𝔽₂) // Module.finrank 𝔽₂ W = m}

lemma natCard_fin_fun (n : ℕ) : Nat.card (Fin n → 𝔽₂) = 2 ^ n := by
  rw [Module.natCard_eq_pow_finrank (K := 𝔽₂), Nat.card_zmod, Module.finrank_pi]
  simp

lemma natCard_submodule_eq (n : ℕ) (W : Submodule 𝔽₂ (Fin n → 𝔽₂)) :
    Nat.card ↥W = 2 ^ Module.finrank 𝔽₂ W := by
  rw [Module.natCard_eq_pow_finrank (K := 𝔽₂), Nat.card_zmod]

theorem linIndep_card_fin (n m : ℕ) :
    Nat.card {f : Fin m → (Fin n → 𝔽₂) // LinearIndependent 𝔽₂ f} =
      ∏ i ∈ Finset.range m, (2 ^ n - 2 ^ i) := by
  rw [linIndep_card]
  exact Finset.prod_congr rfl (fun i _ => by rw [natCard_fin_fun])

theorem fiber_card (n m : ℕ) (W : {W : Submodule 𝔽₂ (Fin n → 𝔽₂) //
    Module.finrank 𝔽₂ W = m}) :
    Nat.card {f : Fin m → (Fin n → 𝔽₂) // LinearIndependent 𝔽₂ f ∧
        Submodule.span 𝔽₂ (Set.range f) = W.1} =
      ∏ i ∈ Finset.range m, (2 ^ m - 2 ^ i) := by
  rw [Nat.card_congr (spanFiberEquiv m W.1 W.2), linIndep_card]
  exact Finset.prod_congr rfl (fun i _ => by rw [natCard_submodule_eq, W.2])

/-- Product formula for the Gaussian binomial: multiplying `[n choose m]_2` by the
number of ordered bases of an `m`-dimensional space gives the number of ordered
independent `m`-tuples in `𝔽₂ⁿ`. -/
theorem grCount_mul (n m : ℕ) :
    grCount n m * (∏ i ∈ Finset.range m, (2 ^ m - 2 ^ i)) =
      ∏ i ∈ Finset.range m, (2 ^ n - 2 ^ i) := by
  have h := linIndep_eq_sum (V := Fin n → 𝔽₂) m
  rw [linIndep_card_fin] at h
  rw [Finset.sum_congr rfl (fun W _ => fiber_card n m W)] at h
  rw [Finset.sum_const] at h
  have hsum : (Finset.univ : Finset {W : Submodule 𝔽₂ (Fin n → 𝔽₂) //
        Module.finrank 𝔽₂ W = m}).card • (∏ i ∈ Finset.range m, (2 ^ m - 2 ^ i)) =
      grCount n m * (∏ i ∈ Finset.range m, (2 ^ m - 2 ^ i)) := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card (α := {W : Submodule 𝔽₂ (Fin n → 𝔽₂) //
        Module.finrank 𝔽₂ W = m}), smul_eq_mul]
    rfl
  rw [hsum] at h
  exact h.symm

/-- Lower bound: `2^{m(n-m)} ≤ [n choose m]_2` for `m ≤ n`. -/
theorem grCount_lower (n m : ℕ) (hm : m ≤ n) :
    2 ^ (m * (n - m)) ≤ grCount n m := by
  have hmul := grCount_mul n m
  have hX : 2 ^ (m * (n - m)) = ∏ _i ∈ Finset.range m, 2 ^ (n - m) := by
    rw [Finset.prod_const, Finset.card_range, ← Nat.pow_mul, Nat.mul_comm]
  have hXB : 2 ^ (m * (n - m)) * (∏ i ∈ Finset.range m, (2 ^ m - 2 ^ i)) ≤
      ∏ i ∈ Finset.range m, (2 ^ n - 2 ^ i) := by
    rw [hX, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod
    · intro i _; exact Nat.zero_le _
    · intro i hi
      have h1 : 2 ^ (n - m) * 2 ^ m = 2 ^ n := by
        rw [← Nat.pow_add, Nat.sub_add_cancel hm]
      have h2 : 2 ^ (n - m) * 2 ^ i = 2 ^ ((n - m) + i) := by
        rw [← Nat.pow_add]
      calc 2 ^ (n - m) * (2 ^ m - 2 ^ i)
          = 2 ^ (n - m) * 2 ^ m - 2 ^ (n - m) * 2 ^ i := by rw [Nat.mul_sub_left_distrib]
        _ = 2 ^ n - 2 ^ ((n - m) + i) := by rw [h1, h2]
        _ ≤ 2 ^ n - 2 ^ i := by
            apply Nat.sub_le_sub_left
            exact Nat.pow_le_pow_right (by norm_num) (Nat.le_add_left i (n - m))
  have hBpos : 0 < ∏ i ∈ Finset.range m, (2 ^ m - 2 ^ i) := by
    apply Finset.prod_pos
    intro i hi
    exact Nat.sub_pos_of_lt (Nat.pow_lt_pow_right (by norm_num) (Finset.mem_range.mp hi))
  have hle : 2 ^ (m * (n - m)) * (∏ i ∈ Finset.range m, (2 ^ m - 2 ^ i)) ≤
      grCount n m * (∏ i ∈ Finset.range m, (2 ^ m - 2 ^ i)) := by
    rw [hmul]
    exact hXB
  exact Nat.le_of_mul_le_mul_right hle hBpos

/-- Upper bound: `[n choose m]_2 ≤ 2^{m(n-m)+m}` for `m ≤ n`. -/
theorem grCount_upper (n m : ℕ) (hm : m ≤ n) :
    grCount n m ≤ 2 ^ (m * (n - m) + m) := by
  have hmul := grCount_mul n m
  have hA : ∏ i ∈ Finset.range m, (2 ^ n - 2 ^ i) ≤ 2 ^ (n * m) := by
    calc ∏ i ∈ Finset.range m, (2 ^ n - 2 ^ i) ≤ ∏ _i ∈ Finset.range m, 2 ^ n := by
          apply Finset.prod_le_prod
          · intro i _; exact Nat.zero_le _
          · intro i _; exact Nat.sub_le _ _
      _ = (2 ^ n) ^ m := by rw [Finset.prod_const, Finset.card_range]
      _ = 2 ^ (n * m) := by rw [← Nat.pow_mul]
  have hB : 2 ^ (m * (m - 1)) ≤ ∏ i ∈ Finset.range m, (2 ^ m - 2 ^ i) := by
    calc 2 ^ (m * (m - 1)) = (2 ^ (m - 1)) ^ m := by
          rw [← Nat.pow_mul, Nat.mul_comm]
      _ = ∏ _i ∈ Finset.range m, 2 ^ (m - 1) := by rw [Finset.prod_const, Finset.card_range]
      _ ≤ ∏ i ∈ Finset.range m, (2 ^ m - 2 ^ i) := by
          apply Finset.prod_le_prod
          · intro i _; positivity
          · intro i hi
            have hi' : i ≤ m - 1 := Nat.le_sub_one_of_lt (Finset.mem_range.mp hi)
            have hpow : 2 ^ i ≤ 2 ^ (m - 1) :=
              Nat.pow_le_pow_right (by norm_num) hi'
            have hm1 : 2 ^ m - 2 ^ (m - 1) = 2 ^ (m - 1) := by
              have hpos : 0 < m := Nat.pos_of_ne_zero (by
                rintro rfl
                exact Nat.not_lt_zero i (Finset.mem_range.mp hi))
              obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
              subst hk
              rw [Nat.succ_sub_one, pow_succ, mul_two, Nat.add_sub_cancel]
            calc 2 ^ (m - 1) = 2 ^ m - 2 ^ (m - 1) := hm1.symm
              _ ≤ 2 ^ m - 2 ^ i := Nat.sub_le_sub_left hpow _
  have hExp : m * (n - m) + m + m * (m - 1) = n * m := by
    have h1 : m * (n - m) = n * m - m * m := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_comm m n]
    have h2 : m * (m - 1) = m * m - m := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_one]
    have h3 : m + (m * m - m) = m * m := by
      rw [Nat.add_comm, Nat.sub_add_cancel (Nat.le_mul_self m)]
    rw [h1, h2]
    calc (n * m - m * m) + m + (m * m - m)
        = (n * m - m * m) + (m + (m * m - m)) := by ac_rfl
      _ = (n * m - m * m) + m * m := by rw [h3]
      _ = n * m := Nat.sub_add_cancel (Nat.mul_le_mul_right m hm)
  have hkey : grCount n m * 2 ^ (m * (m - 1)) ≤ 2 ^ (m * (n - m) + m) * 2 ^ (m * (m - 1)) := by
    calc grCount n m * 2 ^ (m * (m - 1))
        ≤ grCount n m * (∏ i ∈ Finset.range m, (2 ^ m - 2 ^ i)) :=
          Nat.mul_le_mul_left _ hB
      _ = ∏ i ∈ Finset.range m, (2 ^ n - 2 ^ i) := hmul
      _ ≤ 2 ^ (n * m) := hA
      _ = 2 ^ (m * (n - m) + m) * 2 ^ (m * (m - 1)) := by
          rw [← Nat.pow_add]
          congr 1
          exact hExp.symm
  exact Nat.le_of_mul_le_mul_right hkey (Nat.pow_pos (by norm_num))

/-! ## Intervals and the Grassmannian -/

section ContainedSubmodules

variable {V' : Type*} [AddCommGroup V'] [Module 𝔽₂ V']

/-- Submodules of `V'` contained in `W0` correspond to submodules of the ambient
space `↥W0`. -/
noncomputable def submoduleLeEquiv (W0 : Submodule 𝔽₂ V') :
    {x : Submodule 𝔽₂ V' // x ≤ W0} ≃ Submodule 𝔽₂ ↥W0 where
  toFun x := x.1.submoduleOf W0
  invFun u := ⟨u.map W0.subtype, by
    rintro _ ⟨v, hv, rfl⟩
    exact v.2⟩
  left_inv x := by
    apply Subtype.ext
    apply le_antisymm
    · rintro _ ⟨⟨v, hvW⟩, hv, rfl⟩
      simpa [Submodule.submoduleOf] using hv
    · intro y hy
      exact ⟨⟨y, x.2 hy⟩, hy, rfl⟩
  right_inv u := by
    apply le_antisymm
    · rintro _ ⟨⟨v, hvW⟩, hv, rfl⟩
      simpa using hv
    · intro v hv
      exact ⟨⟨(v : V'), v.2⟩, by simpa using hv, rfl⟩

/-- Dimension transport across `submoduleLeEquiv`. -/
lemma finrank_submoduleOf {W0 : Submodule 𝔽₂ V'} {x : Submodule 𝔽₂ V'} (h : x ≤ W0) :
    Module.finrank 𝔽₂ (x.submoduleOf W0) = Module.finrank 𝔽₂ x :=
  LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe h)

/-- An `m`-dimensional submodule contained in `W0` is an `m`-dimensional submodule of
the ambient space `↥W0`. -/
noncomputable def submoduleLeFinrankEquiv (W0 : Submodule 𝔽₂ V') (m : ℕ) :
    {x : Submodule 𝔽₂ V' // x ≤ W0 ∧ Module.finrank 𝔽₂ x = m} ≃
      {u : Submodule 𝔽₂ ↥W0 // Module.finrank 𝔽₂ u = m} where
  toFun x := ⟨x.1.submoduleOf W0, by rw [finrank_submoduleOf x.2.1, x.2.2]⟩
  invFun u :=
    ⟨u.1.map W0.subtype, by
      have hle : u.1.map W0.subtype ≤ W0 := by
        rintro _ ⟨v, hv, rfl⟩
        exact v.2
      refine ⟨hle, ?_⟩
      have hcomp : Submodule.comap W0.subtype (u.1.map W0.subtype) = u.1 :=
        Submodule.comap_map_eq_of_injective (Submodule.subtype_injective W0) u.1
      have hfin : Module.finrank 𝔽₂ (Submodule.comap W0.subtype (u.1.map W0.subtype)) =
          Module.finrank 𝔽₂ (u.1.map W0.subtype) :=
        LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hle)
      rw [← hfin, hcomp]
      exact u.2⟩
  left_inv x := by
    apply Subtype.ext
    apply le_antisymm
    · rintro _ ⟨⟨v, hvW⟩, hv, rfl⟩
      simpa [Submodule.submoduleOf] using hv
    · intro y hy
      exact ⟨⟨y, x.2.1 hy⟩, hy, rfl⟩
  right_inv u := by
    apply Subtype.ext
    exact Submodule.comap_map_eq_of_injective (Submodule.subtype_injective W0) u.1

/-- Counting `m`-dimensional submodules contained in `W0` equals counting
`m`-dimensional submodules of the ambient space `↥W0`. -/
theorem card_submodule_le_finrank_eq (W0 : Submodule 𝔽₂ V') (m : ℕ) :
    Nat.card {x : Submodule 𝔽₂ V' // x ≤ W0 ∧ Module.finrank 𝔽₂ x = m} =
      Nat.card {u : Submodule 𝔽₂ ↥W0 // Module.finrank 𝔽₂ u = m} :=
  Nat.card_congr (submoduleLeFinrankEquiv W0 m)

end ContainedSubmodules

/-! ## Specialisation to the Grassmannian -/

section Grassmannian

variable {k ℓ : ℕ}

/-- The number of vertices of `Gr_{k,ℓ}` is the Gaussian binomial `[k choose ℓ]_2`. -/
theorem card_GrVertex_eq_grCount (k ℓ : ℕ) :
    Fintype.card (GrVertex k ℓ) = grCount k ℓ := by
  rw [← Nat.card_eq_fintype_card (α := GrVertex k ℓ)]
  rfl

/-- Lower bound for the number of vertices of `Gr_{k,ℓ}`. -/
theorem card_GrVertex_lower (hm : ℓ ≤ k) :
    2 ^ (ℓ * (k - ℓ)) ≤ Fintype.card (GrVertex k ℓ) := by
  rw [card_GrVertex_eq_grCount]
  exact grCount_lower k ℓ hm

/-- Upper bound for the number of vertices of `Gr_{k,ℓ}`. -/
theorem card_GrVertex_upper (hm : ℓ ≤ k) :
    Fintype.card (GrVertex k ℓ) ≤ 2 ^ (ℓ * (k - ℓ) + ℓ) := by
  rw [card_GrVertex_eq_grCount]
  exact grCount_upper k ℓ hm

/-- The interval count `#(SubGr k ℓ A B)` is a Gaussian binomial in the interval
dimensions `finrank B - finrank A` and `ℓ - finrank A`. -/
theorem card_SubGr_eq_grCount (A B : Submodule 𝔽₂ (Fin k → 𝔽₂)) (hAB : A ≤ B)
    (hℓa : Module.finrank 𝔽₂ A ≤ ℓ) :
    #(SubGr k ℓ A B) = grCount (Module.finrank 𝔽₂ B - Module.finrank 𝔽₂ A)
      (ℓ - Module.finrank 𝔽₂ A) := by
  rw [card_SubGr_eq_quotient A B hAB hℓa]
  rw [card_submodule_le_finrank_eq (Submodule.map A.mkQ B) (ℓ - Module.finrank 𝔽₂ A)]
  rw [grCount]
  exact Commons.LinearAlgebra.Submodule.card_submodule_finrank_eq_of_finrank_eq (K := 𝔽₂)
    (V := ↥(Submodule.map A.mkQ B))
    (V' := Fin (Module.finrank 𝔽₂ B - Module.finrank 𝔽₂ A) → 𝔽₂)
    (by rw [finrank_map_mkQ_of_le A B hAB, Module.finrank_pi, Fintype.card_fin])

/-- Lower bound for the density denominators `#(SubGr k ℓ A B)`. -/
theorem card_SubGr_lower (A B : Submodule 𝔽₂ (Fin k → 𝔽₂)) (hAB : A ≤ B)
    (hℓa : Module.finrank 𝔽₂ A ≤ ℓ) (hℓb : ℓ ≤ Module.finrank 𝔽₂ B) :
    2 ^ ((ℓ - Module.finrank 𝔽₂ A) * (Module.finrank 𝔽₂ B - ℓ)) ≤ #(SubGr k ℓ A B) := by
  rw [card_SubGr_eq_grCount A B hAB hℓa]
  have hm : ℓ - Module.finrank 𝔽₂ A ≤
      Module.finrank 𝔽₂ B - Module.finrank 𝔽₂ A := Nat.sub_le_sub_right hℓb _
  have h := grCount_lower (Module.finrank 𝔽₂ B - Module.finrank 𝔽₂ A)
    (ℓ - Module.finrank 𝔽₂ A) hm
  rw [show (ℓ - Module.finrank 𝔽₂ A) *
      (Module.finrank 𝔽₂ B - Module.finrank 𝔽₂ A - (ℓ - Module.finrank 𝔽₂ A)) =
      (ℓ - Module.finrank 𝔽₂ A) * (Module.finrank 𝔽₂ B - ℓ) from by
        congr 1
        omega] at h
  exact h

/-- Upper bound for the density denominators `#(SubGr k ℓ A B)`. -/
theorem card_SubGr_upper (A B : Submodule 𝔽₂ (Fin k → 𝔽₂)) (hAB : A ≤ B)
    (hℓa : Module.finrank 𝔽₂ A ≤ ℓ) (hℓb : ℓ ≤ Module.finrank 𝔽₂ B) :
    #(SubGr k ℓ A B) ≤ 2 ^ ((ℓ - Module.finrank 𝔽₂ A) * (Module.finrank 𝔽₂ B - ℓ) +
      (ℓ - Module.finrank 𝔽₂ A)) := by
  rw [card_SubGr_eq_grCount A B hAB hℓa]
  have hm : ℓ - Module.finrank 𝔽₂ A ≤
      Module.finrank 𝔽₂ B - Module.finrank 𝔽₂ A := Nat.sub_le_sub_right hℓb _
  have h := grCount_upper (Module.finrank 𝔽₂ B - Module.finrank 𝔽₂ A)
    (ℓ - Module.finrank 𝔽₂ A) hm
  rw [show (ℓ - Module.finrank 𝔽₂ A) *
      (Module.finrank 𝔽₂ B - Module.finrank 𝔽₂ A - (ℓ - Module.finrank 𝔽₂ A)) +
      (ℓ - Module.finrank 𝔽₂ A) =
      (ℓ - Module.finrank 𝔽₂ A) * (Module.finrank 𝔽₂ B - ℓ) +
      (ℓ - Module.finrank 𝔽₂ A) from by
        congr 1
        congr 1
        omega] at h
  exact h

end Grassmannian

/-- `𝔽₂ⁿ` has exactly one `0`-dimensional subspace (the zero subspace). -/
theorem grCount_zero (n : ℕ) : grCount n 0 = 1 := by
  rw [grCount]
  refine Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => ?_⟩, ⟨⟨⊥, finrank_bot _ _⟩⟩⟩
  apply Subtype.ext
  rw [Submodule.finrank_eq_zero.mp a.2, Submodule.finrank_eq_zero.mp b.2]

/-- `𝔽₂ⁿ` has `2^n - 1` one-dimensional subspaces. -/
theorem grCount_one (n : ℕ) : grCount n 1 = 2 ^ n - 1 := by
  have h := grCount_mul n 1
  rw [Finset.prod_range_one, Finset.prod_range_one] at h
  simpa using h

/-- `𝔽₂ⁿ` has exactly one `n`-dimensional subspace (itself). -/
theorem grCount_self (n : ℕ) : grCount n n = 1 := by
  have h := grCount_mul n n
  have hpos : 0 < ∏ i ∈ Finset.range n, (2 ^ n - 2 ^ i) := by
    apply Finset.prod_pos
    intro i hi
    exact Nat.sub_pos_of_lt (Nat.pow_lt_pow_right (by norm_num) (Finset.mem_range.mp hi))
  have h1 : grCount n n * (∏ i ∈ Finset.range n, (2 ^ n - 2 ^ i)) =
      1 * (∏ i ∈ Finset.range n, (2 ^ n - 2 ^ i)) := by
    rw [one_mul]
    exact h
  exact Nat.eq_of_mul_eq_mul_right hpos h1

/-- There is no `m`-dimensional subspace of `𝔽₂ⁿ` when `m > n`. -/
theorem grCount_eq_zero_of_lt {n m : ℕ} (h : n < m) : grCount n m = 0 := by
  classical
  rw [grCount]
  rw [Nat.card_eq_zero]
  left
  refine ⟨fun W => ?_⟩
  have hle : Module.finrank 𝔽₂ W.1 ≤ n := by
    have := Submodule.finrank_le W.1
    rwa [Module.finrank_pi, Fintype.card_fin] at this
  rw [W.2] at hle
  exact absurd hle (not_le_of_gt h)


end F2
end Submission.Grassmann
