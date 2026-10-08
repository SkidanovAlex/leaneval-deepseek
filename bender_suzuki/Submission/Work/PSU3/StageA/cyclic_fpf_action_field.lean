import Mathlib
import Submission.Work.PSU3.StageA.cyclic_regular_action_field

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# A field structure from a fixed-point-free cyclic action

This module supplies `Work.PSU3.StageA.cyclic_fpf_action_field`.  Let `V` be a finite group of
exponent two (so an elementary abelian `2`-group) and let a finite cyclic group `K`, generated
by `k₀`, act on `V` by automorphisms, fixed-point-freely on the non-identity elements, with
`|K| = |V| - 1`.  Then `V` carries a field structure of cardinality `|V|` whose addition is the
group law of `V`, so that `K` embeds in `Fˣ` and acts by multiplication.

The mathematical content is a Singer cycle argument, proved in
`Work.PSU3.StageA.cyclic_regular_action_field`.  Its hypotheses are: a non-identity base point
`e`, that every element of `K` is a *natural* power of `k₀`, that the order of `act k₀` is
`|V| - 1`, and that the powers of `act k₀` are transitive on the non-identity elements.  The
four lemmas below extract those hypotheses from fixed-point-freeness and the cardinality
hypothesis, and additionally upgrade the resulting `ρ : K →* Fˣ` to an injection (a fact the
Singer-cycle lemma does not itself record).
-/

namespace Work.PSU3.StageA

/-- **Faithfulness of a fixed-point-free action.**  If an automorphism coming from `act` fixes a
non-identity element, its argument is trivial (contrapositive of fixed-point-freeness); hence
`act` is injective. -/
theorem fpf_act_injective {V : Type} [Group V]
    {K : Type} [Group K] (act : K →* MulAut V) (e : V) (he : e ≠ 1)
    (hfpf : ∀ k : K, k ≠ 1 → ∀ v : V, act k v = v → v = 1) :
    Function.Injective act := by
  intro a b hab
  by_cases h1 : b⁻¹ * a = 1
  · exact (inv_mul_eq_one.mp h1).symm
  · exfalso
    have h2 : act (b⁻¹ * a) = 1 := by rw [map_mul, map_inv, hab, inv_mul_cancel]
    have h3 : act (b⁻¹ * a) e = e := by
      have := congrArg (fun f : MulAut V => f e) h2
      simpa using this
    exact he (hfpf (b⁻¹ * a) h1 e h3)

/-- **The generator acts with the order of `K`.**  For a generating element `k₀` of a cyclic
group `K`, `orderOf k₀ = Nat.card K`; injectivity of `act` (a consequence of fixed-point
freeness) transports this to `act k₀`. -/
theorem fpf_orderOf_act {V : Type} [Group V]
    {K : Type} [Group K] (act : K →* MulAut V) (k₀ : K) (e : V) (he : e ≠ 1)
    (hgen : Subgroup.zpowers k₀ = ⊤)
    (hfpf : ∀ k : K, k ≠ 1 → ∀ v : V, act k v = v → v = 1) :
    orderOf (act k₀) = Nat.card K := by
  rw [orderOf_injective act (fpf_act_injective act e he hfpf) k₀]
  exact orderOf_eq_card_of_forall_mem_zpowers (fun x => by rw [hgen]; exact Subgroup.mem_top x)

/-- **Natural powers generate the acting group.**  Every element of `K` is an integral power of
`k₀`; since `act k₀` has finite order, every such integral power is a natural power. -/
theorem zpowers_pow_form {V : Type} [Group V] [Fintype V] [DecidableEq V]
    {K : Type} [Group K]
    (act : K →* MulAut V) (k₀ : K) (hgen : Subgroup.zpowers k₀ = ⊤) :
    ∀ k : K, ∃ j : ℕ, act k = act k₀ ^ j := by
  intro k
  have hk : k ∈ Subgroup.zpowers k₀ := by rw [hgen]; exact Subgroup.mem_top k
  rw [Subgroup.mem_zpowers_iff] at hk
  obtain ⟨n, hn⟩ := hk
  refine ⟨(n % (orderOf (act k₀) : ℤ)).toNat, ?_⟩
  have hpos : (orderOf (act k₀) : ℤ) ≠ 0 := by
    have := orderOf_pos (act k₀); omega
  rw [← hn, map_zpow, ← zpow_mod_orderOf,
    ← Int.toNat_of_nonneg (Int.emod_nonneg n hpos)]
  exact zpow_natCast _ _

/-- **Transitivity on the non-identity elements.**  Fixed-point freeness makes the stabiliser of
every non-identity element trivial, so every orbit on `V ∖ {1}` has `|K| = |V| - 1` elements;
a single such orbit therefore exhausts `V ∖ {1}`. -/
theorem fpf_transitive {V : Type} [Group V] [Fintype V] [DecidableEq V]
    {K : Type} [Group K] [Fintype K]
    (act : K →* MulAut V) (hcard : Nat.card K = Nat.card V - 1)
    (hfpf : ∀ k : K, k ≠ 1 → ∀ v : V, act k v = v → v = 1) :
    ∀ e : V, e ≠ 1 → ∀ v : V, v ≠ 1 → ∃ k : K, act k e = v := by
  intro e he v hv
  have hinj : Function.Injective (fun k : K => act k e) := by
    intro k k' h
    have hh : act k e = act k' e := h
    have h1 : act (k'⁻¹ * k) e = e := by
      have h2 : act (k'⁻¹ * k) = (act k')⁻¹ * act k := by rw [map_mul, map_inv]
      rw [h2, MulAut.mul_apply, hh]
      exact MulAut.inv_apply_self V (act k') e
    by_cases hk : k'⁻¹ * k = 1
    · exact (inv_mul_eq_one.mp hk).symm
    · exact absurd (hfpf (k'⁻¹ * k) hk e h1) he
  have hcardimg : (Finset.univ.image (fun k : K => act k e)).card = Fintype.card K := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
  have herase : (Finset.univ.erase (1 : V)).card = Nat.card V - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ (1 : V)), Finset.card_univ,
      Nat.card_eq_fintype_card]
  have hsub : Finset.univ.image (fun k : K => act k e) ⊆ Finset.univ.erase (1 : V) := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨k, -, rfl⟩ := hx
    rw [Finset.mem_erase]
    exact ⟨fun h => he ((act k).injective (by rw [h, map_one])), Finset.mem_univ _⟩
  have hEq : Finset.univ.image (fun k : K => act k e) = Finset.univ.erase (1 : V) := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [hcardimg, herase, ← Nat.card_eq_fintype_card, hcard]
  have hv' : v ∈ Finset.univ.image (fun k : K => act k e) := by
    rw [hEq, Finset.mem_erase]
    exact ⟨hv, Finset.mem_univ _⟩
  rw [Finset.mem_image] at hv'
  obtain ⟨k, -, hk⟩ := hv'
  exact ⟨k, hk⟩

/-- **Field structure from a fixed-point-free cyclic action.**  A finite group `V` of exponent
two carrying a fixed-point-free action of the cyclic group `K = ⟨k₀⟩` of order `|V| - 1` is (the
additive group of) a field of cardinality `|V|`, and `K` embeds in `Fˣ` so that it acts by
multiplication. -/
theorem cyclic_fpf_action_field {V : Type} [Group V] [Fintype V] [DecidableEq V]
    {K : Type} [Group K] [Fintype K]
    (h2 : ∀ x : V, x * x = 1) (act : K →* MulAut V) (k₀ : K)
    (hgen : Subgroup.zpowers k₀ = ⊤)
    (hcard : Nat.card K = Nat.card V - 1)
    (hfpf : ∀ k : K, k ≠ 1 → ∀ v : V, act k v = v → v = 1) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F) (φ : V ≃ F) (ρ : K →* Fˣ),
      Nat.card F = Nat.card V ∧ (∀ a b : V, φ (a * b) = φ a + φ b) ∧
      (∀ (k : K) (v : V), φ (act k v) = (ρ k : F) * φ v) ∧ Function.Injective ρ := by
  classical
  -- `V` is non-trivial: `|K| ≥ 1` forces `|V| ≥ 2`.
  have hV2 : 2 ≤ Nat.card V := by
    have hK : 1 ≤ Nat.card K := by
      rw [Nat.card_eq_fintype_card]; exact Fintype.card_pos_iff.mpr ⟨1⟩
    omega
  obtain ⟨e, he⟩ : ∃ e : V, e ≠ 1 := by
    by_contra h
    push Not at h
    have : Nat.card V ≤ 1 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_le_one_iff_subsingleton]
      exact ⟨fun a b => by rw [h a, h b]⟩
    omega
  -- The four hypotheses of the Singer-cycle lemma.
  have hspan : ∀ k : K, ∃ j : ℕ, act k = act k₀ ^ j := zpowers_pow_form act k₀ hgen
  have hord : orderOf (act k₀) = Nat.card V - 1 := by
    rw [fpf_orderOf_act act k₀ e he hgen hfpf]; exact hcard
  have htrans : ∀ v : V, v ≠ 1 → ∃ i : ℕ, (act k₀ ^ i) e = v := by
    intro v hv
    obtain ⟨k, hk⟩ := fpf_transitive act hcard hfpf e he v hv
    obtain ⟨j, hj⟩ := hspan k
    exact ⟨j, by rw [← hj]; exact hk⟩
  obtain ⟨F, hF, hFin, φ, ρ, hcardF, hadd, heq⟩ :=
    Work.PSU3.StageA.cyclic_regular_action_field h2 act k₀ e he hspan hord htrans
  refine ⟨F, hF, hFin, φ, ρ, hcardF, hadd, heq, ?_⟩
  -- `ρ` is injective: two elements with the same image fix `e`, hence are equal.
  intro a b hrho
  have hker : ρ (b⁻¹ * a) = 1 := by rw [map_mul, map_inv, hrho, inv_mul_cancel]
  have hfixE : act (b⁻¹ * a) e = e := by
    apply φ.injective
    rw [heq (b⁻¹ * a) e, hker]
    simp
  by_cases hab1 : b⁻¹ * a = 1
  · exact (inv_mul_eq_one.mp hab1).symm
  · exact absurd (hfpf (b⁻¹ * a) hab1 e hfixE) he

end Work.PSU3.StageA
