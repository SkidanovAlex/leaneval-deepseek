import Mathlib
import Submission.Grassmann.Regularity
import Submission.Grassmann.GaussianBinomial
import Submission.Commons.LinearAlgebra.Submodule.card_superspaces_finrank_eq_quotient
import Submission.Commons.LinearAlgebra.Submodule.card_submodule_finrank_eq_of_finrank_eq

/-!
# The exact degree of the Grassmann graph `Gr_{k,ℓ}` (Layer 2, quantitative)

`Gr k ℓ` is the graph on the `ℓ`-dimensional subspaces of `𝔽₂ᵏ` in which `L ~ L'` when
`dim (L ⊓ L') = ℓ - 1`.  Its structure is `GL_k(𝔽₂)`-transitive, hence regular
(`Gr_degree_eq`).  Here we compute the common degree:

  `degree L = (2^ℓ - 1) · (2^(k-ℓ+1) - 2)`   (for `1 ≤ ℓ`).

The counting is the classical one:

* every neighbour `L'` of `L` meets `L` in a hyperplane `H = L ⊓ L'` of `L`, and the map
  `L' ↦ (H, L')` is a bijection onto the set of pairs (hyperplane `H ≤ L`,
  `ℓ`-dimensional superspace `L'` of `H` with `L' ≠ L`);
* a subspace `L` of dimension `ℓ ≥ 1` has `2^ℓ - 1` hyperplanes (duality with the
  nonzero functionals `L → 𝔽₂`, i.e. with the `2^ℓ - 1` nonzero vectors of the dual);
* a hyperplane `H ≤ L` (so `finrank H = ℓ - 1`) has `2^(k-ℓ+1) - 1` superspaces of
  dimension `ℓ` (they correspond to the `1`-dimensional subspaces of `𝔽₂ᵏ ⧸ H`), one of
  which is `L`, leaving `2^(k-ℓ+1) - 2`.
-/

open PseudorandomGrassmann
open Module Submodule Finset Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

local notation "𝔽₂" => ZMod 2

namespace Submission.Grassmann
namespace F2

noncomputable section

variable {k ℓ : ℕ}

lemma finrank_fin_fun (n : ℕ) : Module.finrank 𝔽₂ (Fin n → 𝔽₂) = n := by
  rw [Module.finrank_pi]
  simp

/-! ## 1. Hyperplanes over `𝔽₂` and nonzero functionals -/

section Hyperplane

variable {V : Type*} [AddCommGroup V] [Module 𝔽₂ V] [Finite V]

/-- In `𝔽₂` every nonzero element is `1`. -/
lemma zmod2_eq_one {x : 𝔽₂} (h : x ≠ 0) : x = 1 := by
  have hne : x.val ≠ 0 := fun hh => h ((ZMod.val_eq_zero x).mp hh)
  have hlt : x.val < 2 := ZMod.val_lt x
  have h1 : x.val = 1 := by omega
  exact (ZMod.val_eq_one (show 1 < 2 by norm_num) x).mp h1

/-- The `𝔽₂`-linear functionals on a finite `𝔽₂`-space form a finite type. -/
instance instFiniteLinearMap : Finite (V →ₗ[𝔽₂] 𝔽₂) :=
  Finite.of_injective (fun f : V →ₗ[𝔽₂] 𝔽₂ => (f : V → 𝔽₂))
    (fun _ _ h => LinearMap.ext fun x => congrFun h x)

/-- Over `𝔽₂`, two nonzero functionals with the same kernel are equal. -/
lemma eq_of_ker_eq {f g : V →ₗ[𝔽₂] 𝔽₂} (hf : f ≠ 0) (hg : g ≠ 0)
    (h : LinearMap.ker f = LinearMap.ker g) : f = g := by
  classical
  obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
    by_contra hc
    simp only [not_exists, not_not] at hc
    exact hf (LinearMap.ext fun x => by simpa using hc x)
  have hgv : g v ≠ 0 := by
    intro h0
    have h1 : v ∈ LinearMap.ker g := h0
    rw [← h] at h1
    exact hv h1
  have hfv1 : f v = 1 := zmod2_eq_one hv
  have hgv1 : g v = 1 := zmod2_eq_one hgv
  refine LinearMap.ext fun x => ?_
  have hx : x - (f x) • v ∈ LinearMap.ker f := by
    simp only [LinearMap.mem_ker, map_sub, map_smul, hfv1, smul_eq_mul, mul_one, sub_self]
  rw [h] at hx
  have h2 : g x - f x = 0 := by
    simpa only [LinearMap.mem_ker, map_sub, map_smul, hgv1, smul_eq_mul, mul_one] using hx
  have : g x = f x := sub_eq_zero.mp h2
  exact this.symm

/-- The number of nonzero functionals `V →ₗ[𝔽₂] 𝔽₂` is `2 ^ finrank V - 1`. -/
lemma card_nonzero_linearMap :
    Nat.card {f : V →ₗ[𝔽₂] 𝔽₂ // f ≠ 0} = 2 ^ Module.finrank 𝔽₂ V - 1 := by
  classical
  haveI : Fintype (V →ₗ[𝔽₂] 𝔽₂) := Fintype.ofFinite _
  haveI : Fintype {f : V →ₗ[𝔽₂] 𝔽₂ // f ≠ 0} := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card (α := {f : V →ₗ[𝔽₂] 𝔽₂ // f ≠ 0})]
  rw [Fintype.card_subtype]
  rw [show (Finset.univ.filter (fun f : V →ₗ[𝔽₂] 𝔽₂ => f ≠ 0)) = Finset.univ.erase 0 from by
    rw [Finset.filter_ne']]
  rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ]
  rw [← Nat.card_eq_fintype_card (α := V →ₗ[𝔽₂] 𝔽₂)]
  rw [Module.natCard_eq_pow_finrank (K := 𝔽₂) (V := V →ₗ[𝔽₂] 𝔽₂), Nat.card_zmod,
    Module.finrank_linearMap, Module.finrank_self, Nat.mul_one]

/-- The kernel of a nonzero functional is a hyperplane. -/
lemma finrank_ker_eq_pred (f : V →ₗ[𝔽₂] 𝔽₂) (hf : f ≠ 0) :
    Module.finrank 𝔽₂ ↥(LinearMap.ker f) = Module.finrank 𝔽₂ V - 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker f
  have hle : Module.finrank 𝔽₂ ↥(LinearMap.range f) ≤ 1 := by
    have h1 := Submodule.finrank_le (LinearMap.range f : Submodule 𝔽₂ 𝔽₂)
    simpa using h1
  have hne : Module.finrank 𝔽₂ ↥(LinearMap.range f) ≠ 0 := by
    intro h0
    rw [Submodule.finrank_eq_zero] at h0
    exact hf (LinearMap.range_eq_bot.mp h0)
  omega

/-- The isomorphism `V ⧸ H ≃ₗ 𝔽₂` associated with a hyperplane `H`. -/
def hyperplaneQuotEquiv (H : Submodule 𝔽₂ V)
    (hH : Module.finrank 𝔽₂ H = Module.finrank 𝔽₂ V - 1) (hV : 1 ≤ Module.finrank 𝔽₂ V) :
    (V ⧸ H) ≃ₗ[𝔽₂] 𝔽₂ :=
  LinearEquiv.ofFinrankEq (V ⧸ H) 𝔽₂ (by
    have h := Submodule.finrank_quotient_add_finrank H
    rw [Module.finrank_self]
    omega)

/-- A functional whose kernel is a prescribed hyperplane. -/
def hyperplaneFunctional (H : Submodule 𝔽₂ V)
    (hH : Module.finrank 𝔽₂ H = Module.finrank 𝔽₂ V - 1) (hV : 1 ≤ Module.finrank 𝔽₂ V) :
    V →ₗ[𝔽₂] 𝔽₂ :=
  (hyperplaneQuotEquiv H hH hV).toLinearMap.comp H.mkQ

lemma hyperplaneFunctional_ker (H : Submodule 𝔽₂ V)
    (hH : Module.finrank 𝔽₂ H = Module.finrank 𝔽₂ V - 1) (hV : 1 ≤ Module.finrank 𝔽₂ V) :
    LinearMap.ker (hyperplaneFunctional H hH hV) = H := by
  ext x
  rw [LinearMap.mem_ker, hyperplaneFunctional, LinearMap.comp_apply]
  constructor
  · intro h
    have h1 : H.mkQ x = 0 :=
      (hyperplaneQuotEquiv H hH hV).injective
        (h.trans (map_zero (hyperplaneQuotEquiv H hH hV)).symm)
    have h2 : x ∈ LinearMap.ker H.mkQ := h1
    rwa [Submodule.ker_mkQ] at h2
  · intro hx
    have h1 : H.mkQ x = 0 := by
      have h2 : x ∈ LinearMap.ker H.mkQ := by rwa [Submodule.ker_mkQ]
      exact h2
    rw [h1, map_zero]

lemma hyperplaneFunctional_ne_zero (H : Submodule 𝔽₂ V)
    (hH : Module.finrank 𝔽₂ H = Module.finrank 𝔽₂ V - 1) (hV : 1 ≤ Module.finrank 𝔽₂ V) :
    hyperplaneFunctional H hH hV ≠ 0 := by
  intro h0
  have hsurj : Function.Surjective (hyperplaneFunctional H hH hV) := by
    rw [hyperplaneFunctional]
    exact (LinearEquiv.surjective (hyperplaneQuotEquiv H hH hV)).comp
      (Submodule.mkQ_surjective H)
  obtain ⟨x, hx⟩ := hsurj 1
  rw [h0] at hx
  exact one_ne_zero hx.symm

/-- **Hyperplanes over `𝔽₂`**: a finite `𝔽₂`-space of dimension `n ≥ 1` has exactly
`2 ^ n - 1` hyperplanes. -/
theorem card_hyperplane_zmod_two (hV : 1 ≤ Module.finrank 𝔽₂ V) :
    Nat.card {H : Submodule 𝔽₂ V // Module.finrank 𝔽₂ H = Module.finrank 𝔽₂ V - 1} =
      2 ^ Module.finrank 𝔽₂ V - 1 := by
  classical
  haveI : Fintype {f : V →ₗ[𝔽₂] 𝔽₂ // f ≠ 0} := Fintype.ofFinite _
  haveI : Fintype {H : Submodule 𝔽₂ V // Module.finrank 𝔽₂ H = Module.finrank 𝔽₂ V - 1} :=
    Fintype.ofFinite _
  have hle : Nat.card {H : Submodule 𝔽₂ V // Module.finrank 𝔽₂ H = Module.finrank 𝔽₂ V - 1} ≤
      Nat.card {f : V →ₗ[𝔽₂] 𝔽₂ // f ≠ 0} := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    refine Fintype.card_le_of_injective
      (fun H => (⟨hyperplaneFunctional H.1 H.2 hV,
        hyperplaneFunctional_ne_zero H.1 H.2 hV⟩ : {f : V →ₗ[𝔽₂] 𝔽₂ // f ≠ 0})) ?_
    intro H H' h
    have hk : LinearMap.ker (hyperplaneFunctional H.1 H.2 hV) =
        LinearMap.ker (hyperplaneFunctional H'.1 H'.2 hV) :=
      congrArg (fun f : {f : V →ₗ[𝔽₂] 𝔽₂ // f ≠ 0} => LinearMap.ker f.1) h
    rw [hyperplaneFunctional_ker, hyperplaneFunctional_ker] at hk
    exact Subtype.ext hk
  have hge : Nat.card {f : V →ₗ[𝔽₂] 𝔽₂ // f ≠ 0} ≤
      Nat.card {H : Submodule 𝔽₂ V // Module.finrank 𝔽₂ H = Module.finrank 𝔽₂ V - 1} := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    refine Fintype.card_le_of_injective
      (fun f => (⟨LinearMap.ker f.1, finrank_ker_eq_pred f.1 f.2⟩ :
        {H : Submodule 𝔽₂ V // Module.finrank 𝔽₂ H = Module.finrank 𝔽₂ V - 1})) ?_
    intro f g h
    have hk : LinearMap.ker f.1 = LinearMap.ker g.1 := congrArg Subtype.val h
    exact Subtype.ext (eq_of_ker_eq f.2 g.2 hk)
  rw [card_nonzero_linearMap] at hle hge
  omega

end Hyperplane

/-! ## 2. Hyperplanes of a fixed subspace -/

/-- The number of hyperplanes of a subspace `L` of dimension `ℓ ≥ 1`. -/
lemma card_hyperplanes_of (L : Submodule 𝔽₂ (Fin k → 𝔽₂)) (hL : Module.finrank 𝔽₂ L = ℓ)
    (hℓ : 1 ≤ ℓ) :
    Nat.card {H : Submodule 𝔽₂ (Fin k → 𝔽₂) // H ≤ L ∧ Module.finrank 𝔽₂ H = ℓ - 1} =
      2 ^ ℓ - 1 := by
  have h1 : Nat.card {H : Submodule 𝔽₂ (Fin k → 𝔽₂) // H ≤ L ∧ Module.finrank 𝔽₂ H = ℓ - 1} =
      Nat.card {u : Submodule 𝔽₂ ↥L // Module.finrank 𝔽₂ u = ℓ - 1} :=
    card_submodule_le_finrank_eq L (ℓ - 1)
  have h2 : Nat.card {u : Submodule 𝔽₂ ↥L // Module.finrank 𝔽₂ u = ℓ - 1} =
      Nat.card {W : Submodule 𝔽₂ (Fin ℓ → 𝔽₂) // Module.finrank 𝔽₂ W = ℓ - 1} :=
    Commons.LinearAlgebra.Submodule.card_submodule_finrank_eq_of_finrank_eq
      (K := 𝔽₂) (V := ↥L) (V' := Fin ℓ → 𝔽₂) (ℓ := ℓ - 1)
      (by rw [hL, finrank_fin_fun])
  rw [h1, h2]
  have h3 := card_hyperplane_zmod_two (V := Fin ℓ → 𝔽₂)
    (by rw [finrank_fin_fun]; exact hℓ)
  rwa [finrank_fin_fun] at h3

/-! ## 3. The number of `m`-dimensional subspaces of an arbitrary finite `𝔽₂`-space -/

/-- The Gaussian binomial `[ℓ choose (ℓ-1)]_2 = 2^ℓ - 1` (the number of hyperplanes of
`𝔽₂^ℓ`), for `1 ≤ ℓ`. -/
lemma grCount_pred (hℓ : 1 ≤ ℓ) : grCount ℓ (ℓ - 1) = 2 ^ ℓ - 1 := by
  have h := card_hyperplane_zmod_two (V := Fin ℓ → 𝔽₂)
    (by rw [finrank_fin_fun]; exact hℓ)
  rw [finrank_fin_fun] at h
  exact h

/-- The number of `m`-dimensional subspaces of a finite `𝔽₂`-space `W` is the Gaussian
binomial `grCount (finrank W) m`. -/
lemma card_submodule_finrank_eq_grCount (W : Type*) [AddCommGroup W] [Module 𝔽₂ W]
    [Finite W] (m : ℕ) :
    Nat.card {T : Submodule 𝔽₂ W // Module.finrank 𝔽₂ T = m} =
      grCount (Module.finrank 𝔽₂ W) m := by
  have h := Commons.LinearAlgebra.Submodule.card_submodule_finrank_eq_of_finrank_eq
    (K := 𝔽₂) (V := W) (V' := Fin (Module.finrank 𝔽₂ W) → 𝔽₂) (ℓ := m)
    (by rw [finrank_fin_fun])
  rw [h]
  rfl

/-! ## 4. Superspaces of a hyperplane -/

lemma card_subtype_ne {α : Type*} [Fintype α] (a : α) :
    Nat.card {x : α // x ≠ a} = Nat.card α - 1 := by
  classical
  haveI : Fintype {x : α // x ≠ a} := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card (α := {x : α // x ≠ a}), Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype]
  rw [show (Finset.univ.filter (fun x : α => x ≠ a)) = Finset.univ.erase a from by
    rw [Finset.filter_ne']]
  rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ]

/-- A hyperplane `H` of `L` has `2 ^ (k - ℓ + 1) - 1` superspaces of dimension `ℓ` in
`𝔽₂ᵏ` (corresponding to the `1`-dimensional subspaces of `𝔽₂ᵏ ⧸ H`). -/
lemma card_superspaces_hyperplane (H : Submodule 𝔽₂ (Fin k → 𝔽₂))
    (hH : Module.finrank 𝔽₂ H = ℓ - 1) (hk : ℓ ≤ k) (hℓ : 1 ≤ ℓ) :
    Nat.card {L' : Submodule 𝔽₂ (Fin k → 𝔽₂) // H ≤ L' ∧ Module.finrank 𝔽₂ L' = ℓ} =
      2 ^ (k - ℓ + 1) - 1 := by
  have hfin : Module.finrank 𝔽₂ H ≤ ℓ := by omega
  have hpow : Module.finrank 𝔽₂ ((Fin k → 𝔽₂) ⧸ H) = k - ℓ + 1 := by
    have h := Submodule.finrank_quotient_add_finrank H
    rw [finrank_fin_fun, hH] at h
    omega
  rw [Commons.LinearAlgebra.Submodule.card_superspaces_finrank_eq_quotient
    (K := 𝔽₂) (V := Fin k → 𝔽₂) H hfin]
  have hquot : ℓ - Module.finrank 𝔽₂ H = 1 := by omega
  rw [hquot, card_submodule_finrank_eq_grCount ((Fin k → 𝔽₂) ⧸ H) 1, grCount_one, hpow]

/-- The number of `ℓ`-dimensional superspaces of a hyperplane `H ≤ L` other than `L`. -/
lemma card_superspaces_ne (L H : Submodule 𝔽₂ (Fin k → 𝔽₂)) (hHle : H ≤ L)
    (hH : Module.finrank 𝔽₂ H = ℓ - 1) (hL : Module.finrank 𝔽₂ L = ℓ) (hℓ : 1 ≤ ℓ) :
    Nat.card {L' : Submodule 𝔽₂ (Fin k → 𝔽₂) // H ≤ L' ∧ Module.finrank 𝔽₂ L' = ℓ ∧ L' ≠ L} =
      2 ^ (k - ℓ + 1) - 2 := by
  classical
  have hk : ℓ ≤ k := by
    have h := Submodule.finrank_le L
    rw [finrank_fin_fun, hL] at h
    exact h
  have hsup := card_superspaces_hyperplane (k := k) (ℓ := ℓ) H hH hk hℓ
  haveI : Fintype {L' : Submodule 𝔽₂ (Fin k → 𝔽₂) // H ≤ L' ∧ Module.finrank 𝔽₂ L' = ℓ} :=
    Fintype.ofFinite _
  have heq : Nat.card {L' : Submodule 𝔽₂ (Fin k → 𝔽₂) //
        H ≤ L' ∧ Module.finrank 𝔽₂ L' = ℓ ∧ L' ≠ L} =
      Nat.card {x : {L' : Submodule 𝔽₂ (Fin k → 𝔽₂) //
          H ≤ L' ∧ Module.finrank 𝔽₂ L' = ℓ} // x ≠ ⟨L, hHle, hL⟩} :=
    Nat.card_congr
      { toFun := fun L' => ⟨⟨L'.1, L'.2.1, L'.2.2.1⟩,
          fun hh => L'.2.2.2 (congrArg (fun y : {L' : Submodule 𝔽₂ (Fin k → 𝔽₂) //
            H ≤ L' ∧ Module.finrank 𝔽₂ L' = ℓ} => y.1) hh)⟩
        invFun := fun x => ⟨x.1.1, x.1.2.1, x.1.2.2,
          fun hh => x.2 (Subtype.ext hh)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [heq, card_subtype_ne (α := {L' : Submodule 𝔽₂ (Fin k → 𝔽₂) //
    H ≤ L' ∧ Module.finrank 𝔽₂ L' = ℓ}) ⟨L, hHle, hL⟩, hsup, Nat.sub_sub]

/-! ## 5. The neighbours of a vertex -/

/-- The forward map: a neighbour `L'` of `L` gives the hyperplane `L ⊓ L'` of `L`. -/
def nsToFun (L : Submodule 𝔽₂ (Fin k → 𝔽₂)) (hL : Module.finrank 𝔽₂ L = ℓ) (hℓ : 1 ≤ ℓ)
    (L' : {L' : Submodule 𝔽₂ (Fin k → 𝔽₂) // Module.finrank 𝔽₂ L' = ℓ ∧
        Module.finrank 𝔽₂ ↥(L ⊓ L') = ℓ - 1}) :
    Σ (H : {H : Submodule 𝔽₂ (Fin k → 𝔽₂) // H ≤ L ∧ Module.finrank 𝔽₂ H = ℓ - 1}),
      {L' : Submodule 𝔽₂ (Fin k → 𝔽₂) // H.1 ≤ L' ∧ Module.finrank 𝔽₂ L' = ℓ ∧ L' ≠ L} :=
  ⟨⟨L ⊓ L'.1, inf_le_left, L'.2.2⟩,
    ⟨L'.1, inf_le_right, L'.2.1, by
      intro h
      have h1 : Module.finrank 𝔽₂ ↥(L ⊓ L'.1) = ℓ := by rw [h, inf_idem, hL]
      omega⟩⟩

/-- The backward map: a hyperplane `H ≤ L` and an `ℓ`-dimensional superspace `L' ≠ L`
of `H` give the neighbour `L'` of `L`. -/
def nsInvFun (L : Submodule 𝔽₂ (Fin k → 𝔽₂)) (hL : Module.finrank 𝔽₂ L = ℓ) (hℓ : 1 ≤ ℓ)
    (s : Σ (H : {H : Submodule 𝔽₂ (Fin k → 𝔽₂) // H ≤ L ∧ Module.finrank 𝔽₂ H = ℓ - 1}),
        {L' : Submodule 𝔽₂ (Fin k → 𝔽₂) // H.1 ≤ L' ∧ Module.finrank 𝔽₂ L' = ℓ ∧ L' ≠ L}) :
    {L' : Submodule 𝔽₂ (Fin k → 𝔽₂) // Module.finrank 𝔽₂ L' = ℓ ∧
        Module.finrank 𝔽₂ ↥(L ⊓ L') = ℓ - 1} :=
  ⟨s.2.1, s.2.2.2.1, by
    have hle : s.1.1 ≤ L ⊓ s.2.1 := le_inf s.1.2.1 s.2.2.1
    have hne : L ⊓ s.2.1 ≠ L := by
      intro h
      have hLle : L ≤ s.2.1 := le_trans (le_of_eq h.symm) inf_le_right
      exact s.2.2.2.2 (Submodule.eq_of_le_of_finrank_eq hLle (by rw [hL, s.2.2.2.1])).symm
    have hlt : Module.finrank 𝔽₂ ↥(L ⊓ s.2.1) < ℓ := by
      have := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne inf_le_left hne)
      rwa [hL] at this
    have hge : ℓ - 1 ≤ Module.finrank 𝔽₂ ↥(L ⊓ s.2.1) := by
      have := Submodule.finrank_mono hle
      rwa [s.1.2.2] at this
    omega⟩

/-- If `H ≤ L` is a hyperplane of `L` and `L' ≠ L` is an `ℓ`-dimensional superspace of
`H`, then `L ⊓ L' = H`. -/
lemma inf_eq_of_le_of_ne {L H L' : Submodule 𝔽₂ (Fin k → 𝔽₂)}
    (hL : Module.finrank 𝔽₂ L = ℓ) (hH : Module.finrank 𝔽₂ H = ℓ - 1) (hHle : H ≤ L)
    (hHle' : H ≤ L') (hL' : Module.finrank 𝔽₂ L' = ℓ) (hℓ : 1 ≤ ℓ) (hne : L' ≠ L) :
    L ⊓ L' = H := by
  have hne' : L ⊓ L' ≠ L := by
    intro h
    have hLle : L ≤ L' := le_trans (le_of_eq h.symm) inf_le_right
    exact hne (Submodule.eq_of_le_of_finrank_eq hLle (by rw [hL, hL'])).symm
  have hlt : Module.finrank 𝔽₂ ↥(L ⊓ L') < ℓ := by
    have := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne inf_le_left hne')
    rwa [hL] at this
  have hge : ℓ - 1 ≤ Module.finrank 𝔽₂ ↥(L ⊓ L') := by
    have := Submodule.finrank_mono (le_inf hHle hHle')
    rwa [hH] at this
  have heq : Module.finrank 𝔽₂ ↥(L ⊓ L') = ℓ - 1 := by omega
  exact (Submodule.eq_of_le_of_finrank_eq (le_inf hHle hHle') (by rw [hH, heq])).symm

/-- The number of neighbours of a vertex: the two inverse maps between the set of
neighbours and the set of pairs (hyperplane, superspace). -/
lemma card_neighborSubtype (L : Submodule 𝔽₂ (Fin k → 𝔽₂)) (hL : Module.finrank 𝔽₂ L = ℓ)
    (hℓ : 1 ≤ ℓ) :
    Nat.card {L' : Submodule 𝔽₂ (Fin k → 𝔽₂) // Module.finrank 𝔽₂ L' = ℓ ∧
        Module.finrank 𝔽₂ ↥(L ⊓ L') = ℓ - 1} = (2 ^ ℓ - 1) * (2 ^ (k - ℓ + 1) - 2) := by
  classical
  haveI : Fintype {L' : Submodule 𝔽₂ (Fin k → 𝔽₂) // Module.finrank 𝔽₂ L' = ℓ ∧
      Module.finrank 𝔽₂ ↥(L ⊓ L') = ℓ - 1} := Fintype.ofFinite _
  haveI : Fintype (Σ (H : {H : Submodule 𝔽₂ (Fin k → 𝔽₂) //
        H ≤ L ∧ Module.finrank 𝔽₂ H = ℓ - 1}),
      {L' : Submodule 𝔽₂ (Fin k → 𝔽₂) // H.1 ≤ L' ∧ Module.finrank 𝔽₂ L' = ℓ ∧ L' ≠ L}) :=
    Fintype.ofFinite _
  have h1 : Nat.card {L' : Submodule 𝔽₂ (Fin k → 𝔽₂) // Module.finrank 𝔽₂ L' = ℓ ∧
        Module.finrank 𝔽₂ ↥(L ⊓ L') = ℓ - 1} ≤
      Nat.card (Σ (H : {H : Submodule 𝔽₂ (Fin k → 𝔽₂) //
          H ≤ L ∧ Module.finrank 𝔽₂ H = ℓ - 1}),
        {L' : Submodule 𝔽₂ (Fin k → 𝔽₂) // H.1 ≤ L' ∧ Module.finrank 𝔽₂ L' = ℓ ∧ L' ≠ L}) := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    refine Fintype.card_le_of_injective (nsToFun L hL hℓ) ?_
    intro L' L'' h
    have h2 : L'.1 = L''.1 := by
      have := congrArg (fun s => s.2.1) h
      simpa only [nsToFun] using this
    exact Subtype.ext h2
  have h2 : Nat.card (Σ (H : {H : Submodule 𝔽₂ (Fin k → 𝔽₂) //
          H ≤ L ∧ Module.finrank 𝔽₂ H = ℓ - 1}),
        {L' : Submodule 𝔽₂ (Fin k → 𝔽₂) // H.1 ≤ L' ∧ Module.finrank 𝔽₂ L' = ℓ ∧ L' ≠ L}) ≤
      Nat.card {L' : Submodule 𝔽₂ (Fin k → 𝔽₂) // Module.finrank 𝔽₂ L' = ℓ ∧
        Module.finrank 𝔽₂ ↥(L ⊓ L') = ℓ - 1} := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    refine Fintype.card_le_of_injective (nsInvFun L hL hℓ) ?_
    rintro ⟨⟨H, hHle, hHfin⟩, ⟨L', hHle', hL'fin, hne'⟩⟩
      ⟨⟨H₂, hHle₂, hHfin₂⟩, ⟨L'', hHle'', hL''fin, hne''⟩⟩ h
    have hL'eq : L' = L'' := by
      have := congrArg Subtype.val h
      simpa only [nsInvFun] using this
    have hkey : L ⊓ L' = H :=
      inf_eq_of_le_of_ne hL hHfin hHle hHle' hL'fin hℓ hne'
    have hkey₂ : L ⊓ L'' = H₂ :=
      inf_eq_of_le_of_ne hL hHfin₂ hHle₂ hHle'' hL''fin hℓ hne''
    have hHval : H = H₂ := by rw [← hkey, ← hkey₂, hL'eq]
    refine Sigma.ext (Subtype.ext hHval) ?_
    refine (Subtype.heq_iff_coe_eq ?_).mpr ?_
    · intro x
      simp only [Subtype.coe_mk]
      rw [hHval]
    · simpa only [Subtype.coe_mk] using hL'eq
  rw [le_antisymm h1 h2, Nat.card_sigma]
  rw [Finset.sum_congr rfl (fun H _ => card_superspaces_ne L H.1 H.2.1 H.2.2 hL hℓ)]
  rw [Finset.sum_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card (α := {H : Submodule 𝔽₂ (Fin k → 𝔽₂) //
      H ≤ L ∧ Module.finrank 𝔽₂ H = ℓ - 1}), card_hyperplanes_of L hL hℓ, smul_eq_mul]

/-! ## 6. From neighbours of a vertex to the degree -/

lemma card_adj_eq (L : GrVertex k ℓ) (hℓ : 1 ≤ ℓ) :
    Nat.card {L' : GrVertex k ℓ // (Gr k ℓ).Adj L L'} =
      Nat.card {X : Submodule 𝔽₂ (Fin k → 𝔽₂) // Module.finrank 𝔽₂ X = ℓ ∧
        Module.finrank 𝔽₂ ↥(L.1 ⊓ X) = ℓ - 1} := by
  refine Nat.card_congr ?_
  refine
    { toFun := fun L' => ⟨L'.1.1, L'.1.2, ?_⟩
      invFun := fun X => ⟨⟨X.1, X.2.1⟩, ?_⟩
      left_inv := fun L' => Subtype.ext rfl
      right_inv := fun X => Subtype.ext rfl }
  · have h := L'.2
    simp only [Gr, SimpleGraph.fromRel_adj] at h
    rcases h.2 with hh | hh
    · exact hh
    · rwa [inf_comm] at hh
  · simp only [Gr, SimpleGraph.fromRel_adj]
    refine ⟨?_, Or.inl X.2.2⟩
    intro h
    have h1 : L.1 = X.1 := by simpa using congrArg Subtype.val h
    have h2 : Module.finrank 𝔽₂ ↥(L.1 ⊓ X.1) = ℓ := by rw [← h1, inf_idem, L.2]
    omega

open Classical in
/-- **The exact degree of the Grassmann graph**: for `1 ≤ ℓ`, every vertex of `Gr k ℓ` has
degree `(2^ℓ - 1) · (2^(k-ℓ+1) - 2)`. -/
lemma Gr_degree_eq_value (hℓ : 1 ≤ ℓ) (L : GrVertex k ℓ) :
    (Gr k ℓ).degree L = (2 ^ ℓ - 1) * (2 ^ (k - ℓ + 1) - 2) := by
  classical
  have hdeg : Nat.card {L' : GrVertex k ℓ // (Gr k ℓ).Adj L L'} = (Gr k ℓ).degree L := by
    rw [Nat.card_eq_fintype_card,
      ← SimpleGraph.card_neighborSet_eq_degree (G := Gr k ℓ) (v := L)]
    rfl
  rw [← hdeg, card_adj_eq L hℓ, card_neighborSubtype L.1 L.2 hℓ]

end

end F2
end Submission.Grassmann
