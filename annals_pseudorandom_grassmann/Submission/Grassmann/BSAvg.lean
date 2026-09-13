import Submission.Grassmann.BKSHom
import Submission.Grassmann.Regularity
import Submission.Grassmann.ExpansionBound
import Submission.Commons.LinearAlgebra.Dimension.finrank_map_eq_finrank_sub_finrank_inf_ker
import Submission.Commons.LinearAlgebra.Submodule.card_L_inf_comap_eq
import Submission.Commons.LinearAlgebra.Submodule.two_mul_card_inf_comap

/-!
# The BKS averaging step (arXiv:1804.08662 §3): many returns from small expansion

Fix the standard basis `B₀` of `E = 𝔽₂^k`.  A vertex `L ∈ V_ℓ(B₀)` ("good") is one whose
projection to the first `ℓ` coordinates is onto; equivalently `L ⊓ K₀ = ⊥` where
`K₀ = ker (projFirst ℓ k)`.

For an invertible `e : E ≃ₗ E` put `G_e = {L : grMap e L ∈ V_ℓ(B₀)}` ("the good vertices *in
the basis* `e`") — these are exactly the `L` with `L ⊓ comap e K₀ = ⊥`.

Averaging over `e` we show that there is an `e` for which the set `S ∩ G_e` has as many
internal good edges as a random vertex of `S` has neighbours in `S`: this is the point at
which the "small expansion" hypothesis `Φ(S) ≤ α` is converted into the hypothesis of the
Inverse Shortcode Hypothesis (a lower bound on the number of rank-one returns).

The key counting input is `Commons.LinearAlgebra.Submodule.card_inf_bot_pairs`: exactly half of
the transversals of `L` are also transversal to an adjacent `L'`; together with the identity
`deg (Gr k ℓ) = 2 · rankOneCount ℓ (k-ℓ)` this makes the conversion lossless.
-/

open Finset BigOperators Matrix
open Classical
open PseudorandomGrassmann
open Module

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

-- We resolve decidability through the classical instances so that terms such as `Sᶜ`
-- are elaborated exactly as in `Φ` (whose `DecidableEq` came from `Classical.propDecidable`).
attribute [-instance] Subtype.instDecidableEq

variable {k ℓ : ℕ}

/-- The subspace of `𝔽₂^k` killed by the projection onto the first `ℓ` coordinates. -/
def kernFirst (ℓ k : ℕ) : Submodule 𝔽₂ (Fin k → 𝔽₂) := LinearMap.ker (projFirst ℓ k)

lemma projFirst_surjective (ℓ k : ℕ) : Function.Surjective (projFirst ℓ k) := by
  intro y
  refine ⟨fun i => if h : (i : ℕ) < ℓ then y ⟨i, h⟩ else 0, ?_⟩
  funext i
  simp only [projFirst_apply]
  rw [dif_pos i.2]

lemma finrank_kernFirst (h : ℓ ≤ k) : Module.finrank 𝔽₂ (kernFirst ℓ k) = k - ℓ := by
  simp only [kernFirst]
  have hker := LinearMap.finrank_range_add_finrank_ker (projFirst ℓ k)
  have hrange : LinearMap.range (projFirst ℓ k) = ⊤ :=
    LinearMap.range_eq_top.mpr (projFirst_surjective ℓ k)
  rw [hrange, finrank_top, Module.finrank_fintype_fun_eq_card, card_subLt h,
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hker
  exact Nat.eq_sub_of_add_eq (Nat.add_comm _ _ ▸ hker)

/-- A vertex of the Grassmann graph is *good* if its projection to the first `ℓ` coordinates
is onto (i.e. it belongs to `V_ℓ(B₀)`). -/
def IsGood (L : GrVertex k ℓ) : Prop := Submodule.map (projFirst ℓ k) L.1 = ⊤

instance (L : GrVertex k ℓ) : Decidable (IsGood L) := by
  unfold IsGood; infer_instance

/-- Goodness is the same as being transversal to `K₀`. -/
lemma IsGood_iff_inf_bot (h : ℓ ≤ k) (L : GrVertex k ℓ) :
    IsGood L ↔ L.1 ⊓ kernFirst ℓ k = ⊥ := by
  simp only [kernFirst]
  have hdim :=
    Commons.LinearAlgebra.Dimension.finrank_map_eq_finrank_sub_finrank_inf_ker
      (projFirst ℓ k) L.1
  have htop : Module.finrank 𝔽₂ ({i : Fin k // (i : ℕ) < ℓ} → 𝔽₂) = ℓ := by
    rw [Module.finrank_fintype_fun_eq_card, card_subLt h]
  constructor
  · intro hg
    rw [IsGood] at hg
    have h1 : Module.finrank 𝔽₂ ↥(Submodule.map (projFirst ℓ k) L.1) = ℓ := by
      rw [hg, finrank_top]; exact htop
    rw [hdim, L.2] at h1
    have hle : Module.finrank 𝔽₂ ↥(L.1 ⊓ (projFirst ℓ k).ker) ≤ ℓ := by
      calc Module.finrank 𝔽₂ ↥(L.1 ⊓ (projFirst ℓ k).ker)
          ≤ Module.finrank 𝔽₂ ↥L.1 := Submodule.finrank_mono inf_le_left
        _ = ℓ := L.2
    have h0 : Module.finrank 𝔽₂ ↥(L.1 ⊓ (projFirst ℓ k).ker) = 0 := by omega
    exact Submodule.finrank_eq_zero.mp h0
  · intro hg
    apply Submodule.eq_top_of_finrank_eq
    rw [hdim, hg, finrank_bot, L.2, tsub_zero]
    exact htop.symm

instance : Fintype ((Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂)) :=
  Fintype.ofInjective
    (fun e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂) => (e : (Fin k → 𝔽₂) → (Fin k → 𝔽₂)))
    (fun e₁ e₂ hh => LinearEquiv.ext (fun x => congrFun hh x))

lemma map_comap_kernFirst (h : ℓ ≤ k) (e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂)) :
    Submodule.map (e : (Fin k → 𝔽₂) →ₗ[𝔽₂] (Fin k → 𝔽₂))
        (Submodule.comap (e : (Fin k → 𝔽₂) →ₗ[𝔽₂] (Fin k → 𝔽₂)) (kernFirst ℓ k))
      = kernFirst ℓ k := by
  rw [Submodule.map_comap_eq, LinearMap.range_eq_top.mpr e.surjective, top_inf_eq]

/-- `L` is good in the basis `e` iff `L` is transversal to `comap e K₀`. -/
lemma IsGood_grMap_iff (h : ℓ ≤ k) (e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂))
    (L : GrVertex k ℓ) :
    IsGood (F2.grMap e L) ↔ L.1 ⊓ Submodule.comap (e : (Fin k → 𝔽₂) →ₗ[𝔽₂] (Fin k → 𝔽₂))
      (kernFirst ℓ k) = ⊥ := by
  rw [IsGood_iff_inf_bot h (F2.grMap e L), F2.grMap_val]
  simp only [kernFirst]
  have hmap : Submodule.map (e : (Fin k → 𝔽₂) →ₗ[𝔽₂] (Fin k → 𝔽₂))
        (L.1 ⊓ Submodule.comap (e : (Fin k → 𝔽₂) →ₗ[𝔽₂] (Fin k → 𝔽₂)) (projFirst ℓ k).ker)
      = Submodule.map (e : (Fin k → 𝔽₂) →ₗ[𝔽₂] (Fin k → 𝔽₂)) L.1 ⊓ (projFirst ℓ k).ker := by
    rw [Submodule.map_inf (e : (Fin k → 𝔽₂) →ₗ[𝔽₂] (Fin k → 𝔽₂))
        (fun _ _ hh => e.injective hh),
      Submodule.map_comap_eq, LinearMap.range_eq_top.mpr e.surjective, top_inf_eq]
  constructor
  · intro hh
    have h2 : Submodule.map (e : (Fin k → 𝔽₂) →ₗ[𝔽₂] (Fin k → 𝔽₂))
        (L.1 ⊓ Submodule.comap (e : (Fin k → 𝔽₂) →ₗ[𝔽₂] (Fin k → 𝔽₂)) (projFirst ℓ k).ker) = ⊥ := by
      rw [hmap, hh]
    exact (Submodule.map_eq_bot_iff).mp h2
  · intro hh
    rw [← hmap, hh, Submodule.map_bot]

lemma finrank_comap_grMap (h : ℓ ≤ k) (e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂)) :
    Module.finrank 𝔽₂ (Submodule.comap (e : (Fin k → 𝔽₂) →ₗ[𝔽₂] (Fin k → 𝔽₂)) (kernFirst ℓ k))
      = k - ℓ := by
  have h1 : Module.finrank 𝔽₂ ↥(Submodule.comap (e : (Fin k → 𝔽₂) →ₗ[𝔽₂] (Fin k → 𝔽₂))
        (kernFirst ℓ k))
      = Module.finrank 𝔽₂ ↥(Submodule.map (e : (Fin k → 𝔽₂) →ₗ[𝔽₂] (Fin k → 𝔽₂))
        (Submodule.comap (e : (Fin k → 𝔽₂) →ₗ[𝔽₂] (Fin k → 𝔽₂)) (kernFirst ℓ k))) :=
    LinearEquiv.finrank_eq (e.submoduleMap _)
  rw [map_comap_kernFirst h e, finrank_kernFirst h] at h1
  exact h1


/-! ## The counting identities -/

/-- The number of invertible maps for which `L` is good does not depend on `L`. -/
lemma good_card_eq (h : ℓ ≤ k) (L L' : GrVertex k ℓ) :
    Nat.card {e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂) // IsGood (F2.grMap e L)}
      = Nat.card {e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂) // IsGood (F2.grMap e L')} := by
  obtain ⟨e₀, hmap⟩ := F2.exists_grMap_eq L L'
  have hmap' : L.1.map (e₀ : (Fin k → 𝔽₂) →ₗ[𝔽₂] (Fin k → 𝔽₂)) = L'.1 := by
    have hh := congrArg Subtype.val hmap
    simpa [F2.grMap_val] using hh
  have hA : Nat.card {e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂) // IsGood (F2.grMap e L)}
      = Nat.card {e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂) //
          L.1 ⊓ Submodule.comap (e : (Fin k → 𝔽₂) →ₗ[𝔽₂] (Fin k → 𝔽₂)) (kernFirst ℓ k) = ⊥} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun e => IsGood_grMap_iff h e L))
  have hB : Nat.card {e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂) // IsGood (F2.grMap e L')}
      = Nat.card {e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂) //
          L'.1 ⊓ Submodule.comap (e : (Fin k → 𝔽₂) →ₗ[𝔽₂] (Fin k → 𝔽₂)) (kernFirst ℓ k) = ⊥} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun e => IsGood_grMap_iff h e L'))
  rw [hA, hB]
  exact Commons.LinearAlgebra.Submodule.natCard_subtype_inf_comap_eq_of_map_eq
    (kernFirst ℓ k) L.1 L'.1 e₀ hmap'

/-- **The pair count**: for adjacent `L, L'`, exactly half of the maps making `L` good also make
`L'` good. -/
lemma two_mul_goodPair_card (h : ℓ ≤ k) (hℓ : 1 ≤ ℓ) (L L' : GrVertex k ℓ)
    (hadj : (Gr k ℓ).Adj L L') :
    2 * Nat.card {e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂) //
        IsGood (F2.grMap e L) ∧ IsGood (F2.grMap e L')}
      = Nat.card {e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂) // IsGood (F2.grMap e L)} := by
  have hadj' : Module.finrank 𝔽₂ ↥(L.1 ⊓ L'.1) = ℓ - 1 := by
    have hh := hadj
    rw [Gr, SimpleGraph.fromRel] at hh
    rcases hh.2 with h | h
    · exact h
    · rwa [inf_comm] at h
  have h1 : Nat.card {e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂) //
        IsGood (F2.grMap e L) ∧ IsGood (F2.grMap e L')}
      = Nat.card {e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂) //
          L.1 ⊓ Submodule.comap (e : (Fin k → 𝔽₂) →ₗ[𝔽₂] (Fin k → 𝔽₂)) (kernFirst ℓ k) = ⊥ ∧
          L'.1 ⊓ Submodule.comap (e : (Fin k → 𝔽₂) →ₗ[𝔽₂] (Fin k → 𝔽₂)) (kernFirst ℓ k) = ⊥} :=
    Nat.card_congr (Equiv.subtypeEquivRight
      (fun e => and_congr (IsGood_grMap_iff h e L) (IsGood_grMap_iff h e L')))
  have h2 : Nat.card {e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂) // IsGood (F2.grMap e L)}
      = Nat.card {e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂) //
          L.1 ⊓ Submodule.comap (e : (Fin k → 𝔽₂) →ₗ[𝔽₂] (Fin k → 𝔽₂)) (kernFirst ℓ k) = ⊥} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun e => IsGood_grMap_iff h e L))
  rw [h1, h2]
  exact Commons.LinearAlgebra.Submodule.two_mul_card_inf_comap k ℓ hℓ h (kernFirst ℓ k)
    (finrank_kernFirst h) L.1 L'.1 L.2 L'.2 hadj'

/-- The good part of `S`, counted in the basis `e`. -/
def Ynum (S : Finset (GrVertex k ℓ)) (e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂)) : ℕ :=
  ∑ L ∈ S, if IsGood (F2.grMap e L) then 1 else 0

/-- The number of good neighbours outside `S` of the good part of `S`. -/
def Xnum (S : Finset (GrVertex k ℓ)) (e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂)) : ℕ :=
  ∑ L ∈ S, ∑ L' ∈ Sᶜ,
    if (Gr k ℓ).Adj L L' ∧ IsGood (F2.grMap e L) ∧ IsGood (F2.grMap e L') then 1 else 0

lemma sum_Ynum (h : ℓ ≤ k) (S : Finset (GrVertex k ℓ)) {C : ℕ}
    (hC : ∀ L : GrVertex k ℓ,
      Nat.card {e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂) // IsGood (F2.grMap e L)} = C) :
    ∑ e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂), Ynum S e = S.card * C := by
  have h2 : ∀ L ∈ S, (∑ e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂),
      (if IsGood (F2.grMap e L) then 1 else 0)) = C := by
    intro L _
    rw [← hC L, Nat.card_eq_fintype_card, Finset.sum_boole]
    exact (Fintype.card_subtype _).symm
  simp only [Ynum]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl h2, Finset.sum_const, nsmul_eq_mul]
  simp

lemma sum_Xnum (h : ℓ ≤ k) (hℓ : 1 ≤ ℓ) (S : Finset (GrVertex k ℓ)) {C : ℕ}
    (hC : ∀ L : GrVertex k ℓ,
      Nat.card {e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂) // IsGood (F2.grMap e L)} = C) :
    2 * (∑ e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂), Xnum S e)
      = C * ((Gr k ℓ).interedges S Sᶜ).card := by
  have hstep : ∀ e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂), 2 * Xnum S e
      = ∑ L ∈ S, ∑ L' ∈ Sᶜ, 2 * (if (Gr k ℓ).Adj L L'
          ∧ IsGood (F2.grMap e L) ∧ IsGood (F2.grMap e L') then 1 else 0) := by
    intro e
    simp only [Xnum, Finset.mul_sum]
  have hpair : ∀ L L' : GrVertex k ℓ, (Gr k ℓ).Adj L L' →
      (∑ e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂), 2 * (if (Gr k ℓ).Adj L L'
        ∧ IsGood (F2.grMap e L) ∧ IsGood (F2.grMap e L') then 1 else 0)) = C := by
    intro L L' hadj
    have hzero : (∑ e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂), 2 * (if (Gr k ℓ).Adj L L'
        ∧ IsGood (F2.grMap e L) ∧ IsGood (F2.grMap e L') then 1 else 0))
        = ∑ e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂),
          2 * (if IsGood (F2.grMap e L) ∧ IsGood (F2.grMap e L') then 1 else 0) := by
      refine Finset.sum_congr rfl fun e _ => ?_
      by_cases hh : IsGood (F2.grMap e L) ∧ IsGood (F2.grMap e L')
      · rw [if_pos ⟨hadj, hh⟩, if_pos hh]
      · rw [if_neg (fun hc => hh hc.2), if_neg hh]
    have hsum : (∑ e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂),
          2 * (if IsGood (F2.grMap e L) ∧ IsGood (F2.grMap e L') then 1 else 0))
        = 2 * Nat.card {e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂) //
            IsGood (F2.grMap e L) ∧ IsGood (F2.grMap e L')} := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Nat.card_eq_fintype_card, Finset.sum_boole]
      exact (Fintype.card_subtype _).symm
    rw [hzero, hsum, two_mul_goodPair_card h hℓ L L' hadj, hC L]
  have h1 : (2 : ℕ) * (∑ e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂), Xnum S e)
      = ∑ L ∈ S, ∑ L' ∈ Sᶜ, (if (Gr k ℓ).Adj L L' then C else 0) := by
    rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun e _ => hstep e)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun L _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun L' _ => ?_
    by_cases hadj : (Gr k ℓ).Adj L L'
    · rw [if_pos hadj, hpair L L' hadj]
    · rw [if_neg hadj]
      refine Finset.sum_eq_zero fun e _ => ?_
      rw [if_neg (fun hh => hadj hh.1), mul_zero]
  rw [h1, F2.card_interedges_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun L _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun L' _ => ?_
  by_cases hadj : (Gr k ℓ).Adj L L' <;> simp [hadj]

/-- **The averaging step.**  There is a basis in which the good part of `S` has no more external
good edges than the expansion of `S` predicts.

The two counting identities `sum_Ynum` and `sum_Xnum` above reduce this to the arithmetic
identity `∑_e Xnum S e = Φ·N₁·∑_e Ynum S e` (using `deg (Gr k ℓ) = 2·rankOneCount ℓ (k-ℓ)`),
after which the Paley–Zygmund argument gives an `e` with
`Xnum S e ≤ Φ·N₁·Ynum S e` and `Ynum S e > 0`. -/
theorem exists_good_basis (h : ℓ ≤ k) (hℓ : 1 ≤ ℓ) (h2 : 2 * ℓ ≤ k)
    (S : Finset (GrVertex k ℓ)) (hS : S.Nonempty) :
    ∃ e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂), 0 < Ynum S e ∧
      (Xnum S e : ℝ) ≤ ((Φ (Gr k ℓ) S hS : ℚ) : ℝ) * (rankOneCount ℓ (k - ℓ)) * (Ynum S e : ℝ) := by
  classical
  set C := Nat.card {e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂) //
    IsGood (F2.grMap e hS.choose)} with hCdef
  have hC : ∀ L : GrVertex k ℓ,
      Nat.card {e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂) // IsGood (F2.grMap e L)} = C :=
    fun L => good_card_eq h L hS.choose
  have hgood0 : IsGood (VGood.toVertex (graphGood h (0 : Matrix {i : Fin k // (i : ℕ) < ℓ}
      {j : Fin k // ℓ ≤ (j : ℕ)} 𝔽₂))) := (graphGood h 0).map_eq_top
  obtain ⟨e₁, he₁⟩ := F2.exists_grMap_eq hS.choose
    (VGood.toVertex (graphGood h (0 : Matrix {i : Fin k // (i : ℕ) < ℓ}
      {j : Fin k // ℓ ≤ (j : ℕ)} 𝔽₂)))
  have hgood1 : IsGood (F2.grMap e₁ hS.choose) := by rw [he₁]; exact hgood0
  have hCpos : 0 < C := by
    rw [← hC hS.choose, Nat.card_eq_fintype_card]
    exact Fintype.card_pos_iff.mpr ⟨⟨e₁, hgood1⟩⟩
  have hy := sum_Ynum h S hC
  have hx := sum_Xnum h hℓ S hC
  have hSpos : 0 < S.card := Finset.card_pos.mpr hS
  have hdegNat : (2 ^ ℓ - 1) * (2 ^ (k - ℓ + 1) - 2)
      = 2 * ((2 ^ ℓ - 1) * (2 ^ (k - ℓ) - 1)) := by
    have h1 : 2 ^ (k - ℓ + 1) = 2 * 2 ^ (k - ℓ) := by rw [pow_succ]; ring
    have h3 : 2 ^ (k - ℓ + 1) - 2 = 2 * (2 ^ (k - ℓ) - 1) := by
      rw [h1, Nat.mul_sub_left_distrib, Nat.mul_one]
    rw [h3, Nat.mul_left_comm]
  have hdegR : (((Gr k ℓ).degree hS.choose : ℕ) : ℝ) = 2 * (rankOneCount ℓ (k - ℓ)) := by
    rw [F2.Gr_degree_eq_value hℓ, hdegNat, rankOneCount_eq_card]
    push_cast
    ring
  have hdegpos : 0 < (Gr k ℓ).degree hS.choose := by
    rw [F2.Gr_degree_eq_value hℓ, hdegNat]
    have h1 : 1 < 2 ^ ℓ := Nat.one_lt_pow (by omega) (by norm_num)
    have h3 : 1 < 2 ^ (k - ℓ) := Nat.one_lt_pow (by omega) (by norm_num)
    exact Nat.mul_pos (by norm_num) (Nat.mul_pos (Nat.sub_pos_of_lt h1) (Nat.sub_pos_of_lt h3))
  have hdegQ : (((Gr k ℓ).degree hS.choose : ℕ) : ℚ) = F2.degQ k ℓ := by
    rw [F2.Gr_degree_eq_value hℓ, F2.degQ_eq_nat]
  have hΦQ : Φ (Gr k ℓ) S hS * (((Gr k ℓ).degree hS.choose : ℚ) * (S.card : ℚ))
      = ((((Gr k ℓ).interedges S Sᶜ).card : ℕ) : ℚ) := by
    rw [hdegQ, ← mul_assoc]
    exact F2.Phi_mul_deg hℓ S hS
  have hΦR : ((Φ (Gr k ℓ) S hS : ℚ) : ℝ)
      * ((((Gr k ℓ).degree hS.choose : ℕ) : ℝ) * ((S.card : ℕ) : ℝ))
      = (((((Gr k ℓ).interedges S Sᶜ).card : ℕ)) : ℝ) := by
    have hh := congrArg (fun q : ℚ => (q : ℝ)) hΦQ
    push_cast at hh
    simpa [mul_assoc] using hh
  have hYR : ((∑ e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂), Ynum S e : ℕ) : ℝ)
      = (S.card : ℝ) * (C : ℝ) := by
    rw [hy]; push_cast; ring
  have hXR : (2 : ℝ) * ((∑ e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂), Xnum S e : ℕ) : ℝ)
      = (C : ℝ) * (((((Gr k ℓ).interedges S Sᶜ).card : ℕ)) : ℝ) := by
    have hx' : (((C * (((Gr k ℓ).interedges S Sᶜ).card) : ℕ)) : ℝ)
        = 2 * ((∑ e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂), Xnum S e : ℕ) : ℝ) := by
      rw [← hx]; push_cast; ring
    rw [← hx']; push_cast; ring
  have hXtot : ((∑ e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂), Xnum S e : ℕ) : ℝ)
      = ((Φ (Gr k ℓ) S hS : ℚ) : ℝ) * (rankOneCount ℓ (k - ℓ))
        * ((∑ e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂), Ynum S e : ℕ) : ℝ) := by
    have h1 : (2 : ℝ) * ((∑ e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂), Xnum S e : ℕ) : ℝ)
        = 2 * (((Φ (Gr k ℓ) S hS : ℚ) : ℝ) * (rankOneCount ℓ (k - ℓ))
          * ((∑ e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂), Ynum S e : ℕ) : ℝ)) := by
      rw [hXR, ← hΦR, hdegR, hYR]; ring
    linarith [h1]
  set P : ℝ := ((Φ (Gr k ℓ) S hS : ℚ) : ℝ) * (rankOneCount ℓ (k - ℓ)) with hP
  have hex : ∃ e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂), 0 < Ynum S e := by
    by_contra hc
    push_neg at hc
    have h0 : (∑ e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂), Ynum S e) = 0 :=
      Finset.sum_eq_zero fun e _ => Nat.le_zero.mp (hc e)
    rw [h0] at hYR
    have h1 : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hSpos
    have h3 : (0 : ℝ) < (C : ℝ) := by exact_mod_cast hCpos
    nlinarith [hYR]
  have hZ : (∑ e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂),
      (P * (Ynum S e : ℝ) - (Xnum S e : ℝ))) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Nat.cast_sum, ← Nat.cast_sum, hXtot]
    simp only [hP]
    ring
  by_contra hcon
  push_neg at hcon
  obtain ⟨e₀, he₀⟩ := hex
  have hzero : ∀ e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂), Ynum S e = 0 → Xnum S e = 0 := by
    intro e he
    refine Finset.sum_eq_zero fun L hL => ?_
    have hL' : ¬ (L ∈ S ∧ IsGood (F2.grMap e L)) := by
      intro hh
      have h1 : (∑ L ∈ S, (if IsGood (F2.grMap e L) then 1 else 0)) = 0 := he
      have h2 : (if IsGood (F2.grMap e L) then 1 else 0) ≤
          (∑ L ∈ S, (if IsGood (F2.grMap e L) then 1 else 0)) :=
        Finset.single_le_sum (f := fun L => if IsGood (F2.grMap e L) then 1 else 0)
          (fun L _ => by positivity) hL
      rw [h1] at h2
      simp only [if_pos hh.2] at h2
      omega
    rw [Finset.sum_eq_zero]
    intro L' _
    by_cases h1 : (Gr k ℓ).Adj L L' ∧ IsGood (F2.grMap e L) ∧ IsGood (F2.grMap e L')
    · exact absurd ⟨hL, h1.2.1⟩ hL'
    · rw [if_neg h1]
  have hneg : (∑ e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂),
      (P * (Ynum S e : ℝ) - (Xnum S e : ℝ)))
      < (∑ _e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂), (0 : ℝ)) := by
    refine Finset.sum_lt_sum (fun e _ => ?_) ⟨e₀, Finset.mem_univ _, ?_⟩
    · by_cases h : 0 < Ynum S e
      · have hh := hcon e h; linarith
      · have h0 : Ynum S e = 0 := Nat.le_zero.mp (Nat.le_of_not_gt h)
        rw [h0, hzero e h0]; simp
    · have hh := hcon e₀ he₀; linarith
  simp only [Finset.sum_const_zero] at hneg
  linarith [hZ, hneg]

end
end Submission.Grassmann