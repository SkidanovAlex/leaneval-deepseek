import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The centralizer of an irreducible automorphism of an `𝔽₂`-space has size `≤ |Q| - 1`

Let `Q` be a finite nonzero vector space over `𝔽₂ = ZMod 2` and let `σ : Q ≃ₗ[𝔽₂] Q` be an
automorphism whose only `σ`-invariant subspaces are `⊥` and `⊤` (i.e. `Q` is a simple module
over the subalgebra `𝔽₂[σ] ⊆ End Q`).  Then the centralizer of `σ` inside the linear group
`GL(Q) = (Q ≃ₗ[𝔽₂] Q)` has cardinality at most `|Q| - 1`.

The argument is elementary.  By irreducibility, any nonzero vector `v` generates `Q` as an
`𝔽₂[σ]`-module: the span `W` of the orbit `{σ^i v}` is a nonzero `σ`-invariant subspace, hence
`⊤`.  Every element `g` of the centralizer is a linear map commuting with `σ`, so it is
determined by its value on the cyclic generator `v`: `g (σ^i v) = σ^i (g v)`.  Hence the
evaluation map `g ↦ g v` is injective.  Since every centralizer element is invertible, its value
`g v` is nonzero whenever `v ≠ 0`; thus the evaluation map is an injection from the centralizer
into the set of nonzero vectors of `Q`, of size `|Q| - 1`.

(Equality actually holds — the centralizer is the multiplicative group of the field
`𝔽₂[σ] ≅ 𝔽_{2^n}`, of order `2^n - 1 = |Q| - 1` — but only the inequality is needed here.)
-/

set_option linter.style.haveILetI false

namespace Work.ThmF.ChV12

/-- In a finite nontrivial type, the number of elements different from a fixed element is
`Nat.card Q - 1`. -/
private lemma card_ne_zero_subtype {Q : Type} [AddCommGroup Q] [Finite Q] [Nontrivial Q] :
    Nat.card {x : Q // x ≠ 0} = Nat.card Q - 1 := by
  classical
  haveI : Fintype Q := Fintype.ofFinite Q
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype_compl (fun x : Q => x = 0)]
  have : Fintype.card {x : Q // x = 0} = 1 := by
    rw [Fintype.card_eq_one_iff]
    exact ⟨⟨0, rfl⟩, fun y => Subtype.ext y.2⟩
  rw [this]

/-- If `τ` and `σ` commute, then `τ ((σ ^ i) x) = (σ ^ i) (τ x)`. -/
private lemma commute_pow_apply {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (τ σ : M ≃ₗ[ZMod 2] M) (h : τ * σ = σ * τ) (i : ℕ) (x : M) :
    τ ((σ ^ i) x) = (σ ^ i) (τ x) := by
  have h1 : ∀ y : M, τ (σ y) = σ (τ y) := fun y => by
    have := congrArg (fun f : M ≃ₗ[ZMod 2] M => f y) h
    simpa using this
  induction i with
  | zero => simp
  | succ n ih =>
    rw [pow_succ' σ n]
    simp only [LinearEquiv.mul_apply]
    rw [h1 ((σ ^ n) x), ih]

theorem card_centralizer_le_card_sub_one {Q : Type} [AddCommGroup Q] [Module (ZMod 2) Q]
    [Finite Q] [Nontrivial Q] (σ : Q ≃ₗ[ZMod 2] Q)
    (hirr : ∀ W : Submodule (ZMod 2) Q, W ≠ ⊥ → (∀ x ∈ W, σ x ∈ W) → W = ⊤) :
    Nat.card ↥(Subgroup.centralizer ({σ} : Set (Q ≃ₗ[ZMod 2] Q))) ≤ Nat.card Q - 1 := by
  classical
  -- a nonzero vector `v`; its `σ`-orbit spans `Q`
  obtain ⟨v, hv⟩ := exists_ne (0 : Q)
  let S : Set Q := Set.range (fun i : ℕ => (σ ^ i) v)
  let W : Submodule (ZMod 2) Q := Submodule.span (ZMod 2) S
  have hvS : v ∈ S := ⟨0, by simp⟩
  have hSsub : S ⊆ W := Submodule.subset_span
  have hWne : W ≠ ⊥ := by
    intro h
    have : v ∈ (⊥ : Submodule (ZMod 2) Q) := h ▸ hSsub hvS
    exact hv (by simpa using this)
  -- `W` is `σ`-invariant, since `σ '' S ⊆ S`
  have hSσ : σ.toLinearMap '' S ⊆ W := by
    rintro y ⟨z, ⟨i, rfl⟩, rfl⟩
    exact hSsub ⟨i + 1, by
      show (σ ^ (i + 1)) v = σ ((σ ^ i) v)
      rw [pow_succ', LinearEquiv.mul_apply]⟩
  have hmap : W.map σ.toLinearMap ≤ W := by
    rw [Submodule.map_span]
    exact Submodule.span_le.mpr hSσ
  have hWin : ∀ x ∈ W, σ x ∈ W := by
    intro x hx
    have := hmap (Submodule.mem_map_of_mem (f := σ.toLinearMap) hx)
    simpa using this
  have htop : W = ⊤ := hirr W hWne hWin
  -- membership in the centralizer gives commutation with `σ`
  have hcomm : ∀ (g : ↥(Subgroup.centralizer ({σ} : Set (Q ≃ₗ[ZMod 2] Q)))),
      g.1 * σ = σ * g.1 :=
    fun g => (Subgroup.mem_centralizer_singleton_iff).mp g.2
  -- the evaluation map `g ↦ g v` lands in the nonzero vectors
  let f : ↥(Subgroup.centralizer ({σ} : Set (Q ≃ₗ[ZMod 2] Q))) → {x : Q // x ≠ 0} :=
    fun g => ⟨g.1 v, fun h0 => hv (g.1.injective (by rw [h0, map_zero]))⟩
  have hfinj : Function.Injective f := by
    intro g h hgh
    have heq : g.1 v = h.1 v := congrArg Subtype.val hgh
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    -- `g` and `h` agree on the whole orbit of `v`
    have hd0 : ∀ i : ℕ, g.1 ((σ ^ i) v) = h.1 ((σ ^ i) v) := by
      intro i
      rw [commute_pow_apply g.1 σ (hcomm g) i v, heq,
          ← commute_pow_apply h.1 σ (hcomm h) i v]
    -- and hence on its span, which is all of `Q`: `g - h = 0`
    let d : Q →ₗ[ZMod 2] Q := g.1.toLinearMap - h.1.toLinearMap
    have hSker : S ⊆ LinearMap.ker d := by
      rintro y ⟨i, rfl⟩
      refine LinearMap.mem_ker.mpr ?_
      have hh : g.1.toLinearMap ((σ ^ i) v) = h.1.toLinearMap ((σ ^ i) v) := by
        simpa using hd0 i
      show g.1.toLinearMap ((σ ^ i) v) - h.1.toLinearMap ((σ ^ i) v) = 0
      rw [hh, sub_self]
    have hker : LinearMap.ker d = ⊤ := by
      have hle : W ≤ LinearMap.ker d := Submodule.span_le.mpr hSker
      rw [htop] at hle
      exact top_le_iff.mp hle
    have hx : x ∈ LinearMap.ker d := by rw [hker]; trivial
    have hdx : d x = 0 := LinearMap.mem_ker.mp hx
    have h2 : g.1.toLinearMap x = h.1.toLinearMap x := sub_eq_zero.mp hdx
    simpa using h2
  calc Nat.card ↥(Subgroup.centralizer ({σ} : Set (Q ≃ₗ[ZMod 2] Q)))
      ≤ Nat.card {x : Q // x ≠ 0} := Nat.card_le_card_of_injective f hfinj
    _ = Nat.card Q - 1 := card_ne_zero_subtype

end Work.ThmF.ChV12
