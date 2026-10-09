import Mathlib
import Submission.Work.SSGRoute.ZVocab
import Submission.Work.SSGRoute.ZPlace
import Submission.Work.SSGRoute.ZSolves
import Submission.Work.SSGRoute.ZRealV2.escape_v3
import Submission.Work.SSGRoute.ZConstruction.exists_finset_KConj_cover
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester):

Shafarevich Step 4, N2 fix (lead design, ssg8/n2_0001/VERDICT.md). The original grunwald_escape_relative was FALSE (H2935's counterexample: Gal(N/K) = Z/9 × Z/3, K₁ = ⟨x⟩, K₂ = ⟨xy³⟩ have the same Frattini line, so the per-place trichotomies miss the orthogonality on Ann(K₁) + Ann(K₂)). v2 adds hsplit: every additive χ on G_K killing G_{L₁⊔L₂} equals χ₁ + χ₂ with χ_i killing G_{L_i}. That is exactly the false step of the old proof.
REUSE: the GrunwaldEscapeCore/ lane is sorry-free except grunwald_escape_correction, and so are the 18 EscapeCoreLib files, local_kummer_dictionary(_two) and kummerCharHom_eq_one_iff. With hsplit: split χ, handle the χ₂ part place by place via horth₂ and the χ₁ part via reciprocity for g plus horth₁.
additive_split_of_abelian_exponent is pure group theory: if Gal(L₂/K) is abelian of exponent p (and the setup of its statement holds), hsplit follows.
-/

namespace Work.SSGRoute

open _root_.SSGRoute
open scoped Pointwise

/-! ## Small order-theoretic lemmas about additive functions on a subgroup -/

/-- The unit is killed by a function additive on a subgroup. -/
private lemma zrv2_additive_one_eq_zero {Γ M : Type} [Group Γ] [AddCommGroup M] {H : Subgroup Γ}
    {z : Γ → M} (hz : ∀ x ∈ H, ∀ y ∈ H, z (x * y) = z x + z y) : z 1 = 0 := by
  have h : z 1 = z 1 + z 1 := by
    have := hz 1 H.one_mem 1 H.one_mem
    simpa using this
  have h2 : z 1 + 0 = z 1 + z 1 := by rw [add_zero]; exact h
  exact (add_left_cancel h2).symm

/-- The inverse is sent to the negative by a function additive on a subgroup. -/
private lemma zrv2_additive_inv_eq_neg {Γ M : Type} [Group Γ] [AddCommGroup M] {H : Subgroup Γ}
    {z : Γ → M} (hz : ∀ x ∈ H, ∀ y ∈ H, z (x * y) = z x + z y) {y : Γ} (hy : y ∈ H) :
    z y⁻¹ = -z y := by
  have h := hz y hy y⁻¹ (H.inv_mem hy)
  rw [mul_inv_cancel, zrv2_additive_one_eq_zero hz] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- A function additive on a subgroup is invariant under conjugation by elements of it. -/
private lemma zrv2_additive_conj_eq {Γ M : Type} [Group Γ] [AddCommGroup M] {H : Subgroup Γ}
    {z : Γ → M} (hz : ∀ x ∈ H, ∀ y ∈ H, z (x * y) = z x + z y)
    {x y : Γ} (hx : x ∈ H) (hy : y ∈ H) : z (y * x * y⁻¹) = z x := by
  calc z (y * x * y⁻¹) = z (y * x) + z y⁻¹ := hz (y * x) (H.mul_mem hy hx) y⁻¹ (H.inv_mem hy)
    _ = (z y + z x) + z y⁻¹ := by rw [hz y hy x hx]
    _ = (z y + z x) + (-z y) := by rw [zrv2_additive_inv_eq_neg hz hy]
    _ = z x := by abel

/-! ## Enlarging a place set to one place per `K`-class, within the `G_k`-closure -/

/-- **A finite set of representatives of the `G_K`-classes inside the `G_k`-closure of `S'`.**

Given a finite set `S'` of pairwise `G_k`-non-conjugate finite places of `Ω`, there is a finite set
`T` of pairwise `G_K`-non-conjugate places such that

* every element of `T` is `G_k`-conjugate to an element of `S'`,
* every place `G_k`-conjugate to an element of `S'` is `G_K`-conjugate to an element of `T`.

This is the "expand `S₀` to one place per prime of `K`" step of the argument: the closedness
conjunct is what makes the orthogonality hypotheses of `grunwald_escape_relative_v2` verifiable. -/
private theorem zrv2_exists_KConj_cover_closed (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (S' : Finset (ValuationSubring Ω))
    (hS'fin : ∀ A ∈ S', IsFinPlace k A)
    (hS'disj : ∀ A ∈ S', ∀ B ∈ S', IsConjPlace k A B → A = B) :
    ∃ T : Finset (ValuationSubring Ω),
      (∀ A ∈ T, IsFinPlace k A) ∧
      (∀ A ∈ T, ∀ B ∈ T, KConj K A B → A = B) ∧
      (∀ A ∈ T, ∃ A₀ ∈ S', IsConjPlace k A₀ A) ∧
      (∀ B : ValuationSubring Ω, IsFinPlace k B →
        (∃ A₀ ∈ S', IsConjPlace k A₀ B) → ∃ A ∈ T, KConj K A B) := by
  classical
  obtain ⟨T'', hT''fin, hT''disj, -, hT''cov⟩ :=
    ZConstruction.exists_finset_KConj_cover 2 k Ω K
      (∅ : Finset (ValuationSubring Ω)) S' (by intro A hA; simp at hA)
      (by intro A hA; simp at hA) hS'fin hS'disj
  refine ⟨T''.filter (fun A => ∃ A₀ ∈ S', IsConjPlace k A₀ A), ?_, ?_, ?_, ?_⟩
  · intro A hA
    exact hT''fin A (Finset.mem_filter.mp hA).1
  · intro A hA B hB hAB
    exact hT''disj A (Finset.mem_filter.mp hA).1 B (Finset.mem_filter.mp hB).1 hAB
  · intro A hA
    exact (Finset.mem_filter.mp hA).2
  · intro B hBfin hBconj
    obtain ⟨A, hA, hAB⟩ := hT''cov B hBfin hBconj
    refine ⟨A, Finset.mem_filter.mpr ⟨hA, ?_⟩, hAB⟩
    obtain ⟨A₀, hA₀, hA₀B⟩ := hBconj
    exact ⟨A₀, hA₀,
      isConjPlace_trans hA₀B (isConjPlace_symm (ZConstruction.kConj_isConjPlace hAB))⟩

/-! ## Translation of the local group along `G_K`-conjugacy of places -/

/-- If `B = τ • A` with `τ ∈ G_K` and `σ` stabilises `B`, then `τ⁻¹ σ τ` stabilises `A`. -/
private lemma zrv2_inv_conj_mem_decomp {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    {A B : ValuationSubring Ω} {τ σ : Ω ≃ₐ[k] Ω} (hτA : τ • A = B)
    (hσ : σ ∈ decomp k B) : τ⁻¹ * σ * τ ∈ decomp k A := by
  have hfix : σ • B = B := hσ
  show (τ⁻¹ * σ * τ) • A = A
  rw [mul_smul, mul_smul, hτA, hfix, ← hτA, inv_smul_smul]

set_option linter.style.haveILetI false in
/-- **Extension of an additive functional.**  Let `M` be an abelian group whose quotient by `B'` is
of exponent `p`, and let `f : M →+ ZMod p` vanish on `A' ⊓ B'`.  Then there is `F : M →+ ZMod p`
vanishing on `B'` and agreeing with `f` on `A'`. -/
private theorem zrv2_exists_addHom_eq_on_of_kills (p : ℕ) [Fact p.Prime] {M : Type} [AddCommGroup M]
    (B' : AddSubgroup M) (hpt : ∀ x : M, p • x ∈ B')
    (A' : AddSubgroup M) (f : M →+ ZMod p) (hf : ∀ x ∈ A' ⊓ B', f x = 0) :
    ∃ F : M →+ ZMod p, (∀ x ∈ B', F x = 0) ∧ ∀ x ∈ A', F x = f x := by
  classical
  haveI hV : Module (ZMod p) (M ⧸ B') := QuotientAddGroup.zmodModule hpt
  let π : M →+ M ⧸ B' := QuotientAddGroup.mk' B'
  let H : Submodule (ZMod p) (M ⧸ B') := (AddSubgroup.map π A').toZModSubmodule p
  have hHmem : ∀ a ∈ A', π a ∈ H := fun a ha =>
    AddSubgroup.mem_map.mpr ⟨a, ha, rfl⟩
  have hex : ∀ h : H, ∃ a ∈ A', π a = (h : M ⧸ B') := by
    intro h
    exact AddSubgroup.mem_map.mp h.2
  choose a ha_mem ha_pi using hex
  have key : ∀ (h : H) (x : M), x ∈ A' → π x = (h : M ⧸ B') → f x = f (a h) := by
    intro h x hx hpx
    have hk : x - a h ∈ B' := by
      have h1 : π (x - a h) = 0 := by
        rw [map_sub, hpx, ← ha_pi h, sub_self]
      exact (QuotientAddGroup.eq_zero_iff (x - a h)).mp h1
    have hmem : x - a h ∈ A' ⊓ B' := ⟨A'.sub_mem hx (ha_mem h), hk⟩
    have h0 : f (x - a h) = 0 := hf _ hmem
    rw [map_sub] at h0
    exact sub_eq_zero.mp h0
  let ψ : H →+ ZMod p := AddMonoidHom.mk' (fun h => f (a h)) (fun h₁ h₂ => by
    have hx : a h₁ + a h₂ ∈ A' := A'.add_mem (ha_mem h₁) (ha_mem h₂)
    have hpx : π (a h₁ + a h₂) = ((h₁ + h₂ : H) : M ⧸ B') := by
      rw [map_add, ha_pi h₁, ha_pi h₂]
      rfl
    rw [← key (h₁ + h₂) (a h₁ + a h₂) hx hpx, map_add])
  obtain ⟨Ψ, hΨ⟩ := LinearMap.dualMap_surjective_of_injective (Submodule.injective_subtype H)
    (ψ.toZModLinearMap p)
  have hΨapp : ∀ h : H, Ψ (h : M ⧸ B') = ψ h := by
    intro h
    have h1 := LinearMap.congr_fun hΨ h
    simpa using h1
  refine ⟨Ψ.toAddMonoidHom.comp π, ?_, ?_⟩
  · intro x hx
    have h1 : π x = (0 : M ⧸ B') := (QuotientAddGroup.eq_zero_iff x).mpr hx
    show Ψ (π x) = 0
    rw [h1, map_zero]
  · intro x hx
    show Ψ (π x) = f x
    have h1 : π x = ((⟨π x, hHmem x hx⟩ : H) : M ⧸ B') := rfl
    rw [h1, hΨapp, show ψ ⟨π x, hHmem x hx⟩ = f (a ⟨π x, hHmem x hx⟩) from rfl,
      ← key ⟨π x, hHmem x hx⟩ x hx rfl]

/-- **Splitting.**  `χ` additive on `G`, vanishing on `A ⊓ B`, with `G/B` an abelian group of
exponent `p`; then `χ = χ₁ + χ₂` on `G` with `χ₁` vanishing on `A` and `χ₂` on `B`. -/
private theorem zrv2_split_aux (p : ℕ) [Fact p.Prime] {Γ : Type} [Group Γ] (G A B : Subgroup Γ)
    (hBG : B ≤ G) (hAG : A ≤ G)
    (hexp : ∀ σ ∈ G, σ ^ p ∈ B)
    (hcom : ∀ σ ∈ G, ∀ τ ∈ G, σ * τ * σ⁻¹ * τ⁻¹ ∈ B)
    (χ : Γ → ZMod p) (hχ : ∀ x ∈ G, ∀ y ∈ G, χ (x * y) = χ x + χ y)
    (hχ0 : ∀ σ ∈ A ⊓ B, χ σ = 0) :
    ∃ χ₁ χ₂ : Γ → ZMod p,
      (∀ x ∈ G, ∀ y ∈ G, χ₁ (x * y) = χ₁ x + χ₁ y) ∧
      (∀ σ ∈ A, χ₁ σ = 0) ∧
      (∀ x ∈ G, ∀ y ∈ G, χ₂ (x * y) = χ₂ x + χ₂ y) ∧
      (∀ σ ∈ B, χ₂ σ = 0) ∧
      ∀ σ ∈ G, χ σ = χ₁ σ + χ₂ σ := by
  classical
  have hχ1 : χ 1 = 0 := by
    have h : χ 1 = χ 1 + χ 1 := by simpa using hχ 1 G.one_mem 1 G.one_mem
    have h2 : χ 1 + 0 = χ 1 + χ 1 := by rw [add_zero]; exact h
    exact (add_left_cancel h2).symm
  -- `χ` as a multiplicative homomorphism on `↥G`
  let χh : ↥G →* Multiplicative (ZMod p) :=
    { toFun := fun σ => Multiplicative.ofAdd (χ σ)
      map_one' := by
        show Multiplicative.ofAdd (χ 1) = 1
        rw [hχ1]; rfl
      map_mul' := fun σ τ => by
        show Multiplicative.ofAdd (χ (σ * τ))
          = Multiplicative.ofAdd (χ σ) * Multiplicative.ofAdd (χ τ)
        rw [hχ σ σ.2 τ τ.2]; rfl }
  -- the abelianization of `G` and the induced global functional
  let φ : Abelianization ↥G →* Multiplicative (ZMod p) := Abelianization.lift χh
  let f : Additive (Abelianization ↥G) →+ ZMod p :=
    { toFun := fun x => (φ (Additive.toMul x)).toAdd
      map_zero' := by
        show (φ (Additive.toMul (0 : Additive (Abelianization ↥G)))).toAdd = 0
        rw [show Additive.toMul (0 : Additive (Abelianization ↥G)) = 1 from rfl, map_one]
        rfl
      map_add' := fun x y => by
        show (φ (Additive.toMul (x + y))).toAdd
          = (φ (Additive.toMul x)).toAdd + (φ (Additive.toMul y)).toAdd
        rw [toMul_add, map_mul]
        rfl }
  have hf_q : ∀ σ : ↥G, f (Additive.ofMul (Abelianization.of σ)) = χ σ := by
    intro σ
    show (φ (Additive.toMul (Additive.ofMul (Abelianization.of σ)))).toAdd = χ σ
    rw [show Additive.toMul (Additive.ofMul (Abelianization.of σ)) = Abelianization.of σ
      from rfl, Abelianization.lift_apply_of]
    rfl
  -- the subgroups `A'`, `B'` of the abelianization
  have hq_surj : ∀ y : Abelianization ↥G, ∃ σ : ↥G, Abelianization.of σ = y := fun y =>
    QuotientGroup.mk'_surjective (commutator ↥G) y
  have hpt : ∀ x : Additive (Abelianization ↥G),
      p • x ∈ Subgroup.toAddSubgroup ((B.subgroupOf G).map (Abelianization.of (G := ↥G))) := by
    intro x
    obtain ⟨y, rfl⟩ : ∃ y : Abelianization ↥G, Additive.ofMul y = x :=
      ⟨Additive.toMul x, by simp⟩
    obtain ⟨σ, rfl⟩ := hq_surj y
    rw [← ofMul_pow]
    rw [Additive.mem_toAddSubgroup]
    exact Subgroup.mem_map.mpr ⟨σ ^ p, hexp σ σ.2, map_pow (Abelianization.of (G := ↥G)) σ p⟩
  have hker : commutator ↥G ≤ B.subgroupOf G := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    exact hcom (x : Γ) x.2 (y : Γ) y.2
  have hf : ∀ x ∈ Subgroup.toAddSubgroup ((A.subgroupOf G).map (Abelianization.of (G := ↥G))) ⊓
      Subgroup.toAddSubgroup ((B.subgroupOf G).map (Abelianization.of (G := ↥G))), f x = 0 := by
    intro x hx
    obtain ⟨hxA, hxB⟩ := hx
    have hxA1 : Additive.toMul x ∈ (A.subgroupOf G).map (Abelianization.of (G := ↥G)) :=
      (Additive.mem_toAddSubgroup ((A.subgroupOf G).map (Abelianization.of (G := ↥G))) x).mp hxA
    have hxB1 : Additive.toMul x ∈ (B.subgroupOf G).map (Abelianization.of (G := ↥G)) :=
      (Additive.mem_toAddSubgroup ((B.subgroupOf G).map (Abelianization.of (G := ↥G))) x).mp hxB
    obtain ⟨a, ha, haq⟩ := Subgroup.mem_map.mp hxA1
    obtain ⟨b, hb, hbq⟩ := Subgroup.mem_map.mp hxB1
    have hxval : f x = χ (a : Γ) := by
      have h1 : x = Additive.ofMul (Abelianization.of a) := by
        rw [haq]
        rfl
      rw [h1, hf_q]
    rw [hxval]
    have hab : a * b⁻¹ ∈ B.subgroupOf G := by
      have h1 : Abelianization.of (G := ↥G) (a * b⁻¹) = 1 := by
        rw [map_mul, map_inv, haq, hbq, mul_inv_cancel]
      have h2 : a * b⁻¹ ∈ (Abelianization.of (G := ↥G)).ker := MonoidHom.mem_ker.mpr h1
      rw [Abelianization.ker_of] at h2
      exact hker h2
    have haB : a ∈ B.subgroupOf G := by
      have h3 : (a * b⁻¹) * b ∈ B.subgroupOf G := (B.subgroupOf G).mul_mem hab hb
      simpa [mul_assoc] using h3
    have haA : a ∈ A.subgroupOf G := ha
    rw [Subgroup.mem_subgroupOf] at haA haB
    exact hχ0 _ ⟨haA, haB⟩
  obtain ⟨F, hFB, hFA⟩ := zrv2_exists_addHom_eq_on_of_kills p
    (Subgroup.toAddSubgroup ((B.subgroupOf G).map (Abelianization.of (G := ↥G)))) hpt
    (Subgroup.toAddSubgroup ((A.subgroupOf G).map (Abelianization.of (G := ↥G)))) f hf
  have hFA' : ∀ a : ↥G, a ∈ A.subgroupOf G → F (Additive.ofMul (Abelianization.of a)) = χ a := by
    intro a ha
    have h1 : F (Additive.ofMul (Abelianization.of a)) = f (Additive.ofMul (Abelianization.of a)) :=
      hFA _ (by
        rw [Additive.mem_toAddSubgroup, Subgroup.mem_map]
        exact ⟨a, ha, rfl⟩)
    rw [h1, hf_q]
  have hFB' : ∀ b : ↥G, b ∈ B.subgroupOf G → F (Additive.ofMul (Abelianization.of b)) = 0 := by
    intro b hb
    exact hFB _ (by
      rw [Additive.mem_toAddSubgroup, Subgroup.mem_map]
      exact ⟨b, hb, rfl⟩)
  refine ⟨fun σ => if h : σ ∈ G then χ σ - F (Additive.ofMul (Abelianization.of ⟨σ, h⟩)) else 0,
          fun σ => if h : σ ∈ G then F (Additive.ofMul (Abelianization.of ⟨σ, h⟩)) else 0,
          ?_, ?_, ?_, ?_, ?_⟩
  · -- `χ₁` additive
    intro x hx y hy
    have hxy : x * y ∈ G := G.mul_mem hx hy
    dsimp only []
    rw [dif_pos hxy, dif_pos hx, dif_pos hy]
    have h2 : (Additive.ofMul (Abelianization.of (⟨x * y, hxy⟩ : ↥G)) : Additive (Abelianization ↥G))
        = Additive.ofMul (Abelianization.of (⟨x, hx⟩ : ↥G))
          + Additive.ofMul (Abelianization.of (⟨y, hy⟩ : ↥G)) := by
      have e : (⟨x * y, hxy⟩ : ↥G) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
      rw [e, map_mul, ofMul_mul]
    rw [h2, map_add, hχ x hx y hy]
    abel
  · -- `χ₁` kills `A`
    intro σ hσ
    have hσG : σ ∈ G := hAG hσ
    dsimp only []
    rw [dif_pos hσG]
    have h1 : F (Additive.ofMul (Abelianization.of (⟨σ, hσG⟩ : ↥G))) = χ σ :=
      hFA' ⟨σ, hσG⟩ (by rw [Subgroup.mem_subgroupOf]; exact hσ)
    rw [h1]
    exact sub_eq_zero.mpr rfl
  · -- `χ₂` additive
    intro x hx y hy
    have hxy : x * y ∈ G := G.mul_mem hx hy
    dsimp only []
    rw [dif_pos hxy, dif_pos hx, dif_pos hy]
    have h2 : (Additive.ofMul (Abelianization.of (⟨x * y, hxy⟩ : ↥G)) : Additive (Abelianization ↥G))
        = Additive.ofMul (Abelianization.of (⟨x, hx⟩ : ↥G))
          + Additive.ofMul (Abelianization.of (⟨y, hy⟩ : ↥G)) := by
      have e : (⟨x * y, hxy⟩ : ↥G) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
      rw [e, map_mul, ofMul_mul]
    rw [h2, map_add]
  · -- `χ₂` kills `B`
    intro σ hσ
    have hσG : σ ∈ G := hBG hσ
    dsimp only []
    rw [dif_pos hσG]
    exact hFB' ⟨σ, hσG⟩ (by rw [Subgroup.mem_subgroupOf]; exact hσ)
  · -- the sum property
    intro σ hσ
    dsimp only []
    rw [dif_pos hσ, dif_pos hσ]
    abel

/-! ## My own copy of the escape theorem, called with named arguments

The file `Submission/Work/SSGRoute/ZRealV2/escape_hsplit.lean` contains a verbatim copy of the
statement of `Work.SSGRoute.grunwald_escape_relative_v2` (with the same binder names), whose proof
calls my own copy `Work.SSGRoute.ZRealV2.alpha_fixes_inf_hsplit` of the orthogonality
`Work.SSGRoute.N2v2.alpha_fixes_inf_ssg8_hsplit` instead of the lane's.  This wrapper keeps a
stable copy of the statement in my file and calls that theorem by name, so that this node depends
only on its own chain. -/

/-- Grünwald with escape, restated in my own file (same statement as
`Work.SSGRoute.grunwald_escape_relative_v2`). -/
private theorem zrv2_escape (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (hKimag : p = 2 → ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → c = 1)
    (L₁ L₂ : IntermediateField k Ω) [FiniteDimensional k L₁] [IsGalois k L₁]
    [FiniteDimensional k L₂] [IsGalois k L₂] (hKL₁ : K ≤ L₁) (hKL₂ : K ≤ L₂)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T, (∃ τ ∈ K.fixingSubgroup, τ • A = B) → A = B)
    (hTcov : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (B.valuation (p : Ω) < 1 ∨
        (∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ σ ∉ L₁.fixingSubgroup) ∨
        (∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ σ ∉ L₂.fixingSubgroup)) →
      ∃ A ∈ T, ∃ τ ∈ K.fixingSubgroup, τ • A = B)
    (g : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hg : ∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, g (x * y) = g x + g y)
    (hgc : SSGRoute.IsLocConstOn K.fixingSubgroup g)
    (hgram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ T, ∀ τ ∈ K.fixingSubgroup, τ • A ≠ B) → ¬ SSGRoute.IsSplitIn k L₁ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → g σ = 0)
    (h : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p)
    (hh : ∀ A ∈ T, ∀ x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      ∀ y ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A (x * y) = h A x + h A y)
    (hhc : ∀ A ∈ T, ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
      ∀ x ∈ U, x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup → h A x = 0)
    (horth₁ : ∀ A ∈ T,
      (∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A σ = 0) ∨
      (∀ χ : (Ω ≃ₐ[k] Ω) → ZMod p,
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
        (∀ σ ∈ L₁.fixingSubgroup, χ σ = 0) →
        ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, χ σ = 0) ∨
      ((∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → h A σ = 0) ∧
        ∀ χ : (Ω ≃ₐ[k] Ω) → ZMod p,
          (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
          (∀ σ ∈ L₁.fixingSubgroup, χ σ = 0) →
          ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → χ σ = 0))
    (horth₂ : ∀ A ∈ T,
      (∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, g σ + h A σ = 0) ∨
      (∀ χ : (Ω ≃ₐ[k] Ω) → ZMod p,
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
        (∀ σ ∈ L₂.fixingSubgroup, χ σ = 0) →
        ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, χ σ = 0) ∨
      ((∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → g σ + h A σ = 0) ∧
        ∀ χ : (Ω ≃ₐ[k] Ω) → ZMod p,
          (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
          (∀ σ ∈ L₂.fixingSubgroup, χ σ = 0) →
          ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → χ σ = 0))
    (hsplit : ∀ χ : (Ω ≃ₐ[k] Ω) → ZMod p,
      (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
      (∀ σ ∈ (L₁ ⊔ L₂).fixingSubgroup, χ σ = 0) →
      ∃ χ₁ χ₂ : (Ω ≃ₐ[k] Ω) → ZMod p,
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ₁ (x * y) = χ₁ x + χ₁ y) ∧
        (∀ σ ∈ L₁.fixingSubgroup, χ₁ σ = 0) ∧
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ₂ (x * y) = χ₂ x + χ₂ y) ∧
        (∀ σ ∈ L₂.fixingSubgroup, χ₂ σ = 0) ∧
        ∀ σ ∈ K.fixingSubgroup, χ σ = χ₁ σ + χ₂ σ) :
    ∃ (z : (Ω ≃ₐ[k] Ω) → ZMod p) (Q : ValuationSubring Ω),
      SSGRoute.IsFinPlace k Q ∧ SSGRoute.IsSplitIn k (L₁ ⊔ L₂) Q ∧
      (∀ A ∈ T, ∀ τ ∈ K.fixingSubgroup, τ • A ≠ Q) ∧
      (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, z (x * y) = z x + z y) ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ A ∈ T, ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, z σ = g σ + h A σ) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ T, ∀ τ ∈ K.fixingSubgroup, τ • A ≠ B) →
        (∀ τ ∈ K.fixingSubgroup, τ • Q ≠ B) →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) :=
  Work.SSGRoute.ZRealV2.grunwald_escape_v3 (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ) (hζ := hζ)
    (hζK := hζK) (hKimag := hKimag) (L₁ := L₁) (L₂ := L₂) (hKL₁ := hKL₁) (hKL₂ := hKL₂)
    (hsplit := hsplit)
    (T := T) (hTfin := hTfin) (hTdisj := hTdisj) (hTcov := hTcov) (g := g) (hg := hg)
    (hgc := hgc) (hgram := hgram) (h := h) (hh := hh) (hhc := hhc) (horth₁ := horth₁)
    (horth₂ := horth₂)

/-! ## The local correction datum -/

/-- The local correction `h` of the realisation step: zero at the classes of `S`, and `-ν`
elsewhere (so that the total prescribed datum `ν + h` is `ν` at the classes of `S` and `0` at the
other classes). -/
private noncomputable def zrv2CorrectionDatum {p : ℕ} {k Ω : Type} [Field k] [Field Ω]
    [Algebra k Ω]
    (S : Finset (ValuationSubring Ω)) (ν : (Ω ≃ₐ[k] Ω) → ZMod p) :
    ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p := by
  classical
  exact fun A σ => if ∃ A' ∈ S, IsConjPlace k A' A then (0 : ZMod p) else -ν σ

/-! ## The realisation step of Schmidt--Wingberg §4 -/

/-- The realisation step of Schmidt--Wingberg §4 (the auxiliary class `ỹ` of the induction on
`dim A`, bottom of p. 18), with the hypotheses the paper actually has.

* `S` is the old place set `T`.
* `S₀ ⊇ S` is the new one, `T'`. Its extra places split completely in `Λ` (they lie in
  `cs(ν)`, `hnew`).
* `L₂` is the auxiliary field `K̃`. It is unramified at the places of `S` (`hL₂`), and `S₀` covers
  its ramification.  `Gal(L₂/K)` is abelian of exponent `p` (`hL₂exp`, `hL₂comm`).  This holds in
  the paper, where `K̃` is the Galois closure over `k` of the field cut out by a class
  `z' : G_K → A'` with `A'` elementary abelian.  It is what makes the paper's injection
  `H¹(ΛK̃|K)^∨ ↪ H¹(Λ|K)^∨ × H¹(K̃|K)^∨` valid; that injection fails for general `K̃`.

The prescribed datum is `ν` at the classes of `S` and `0` at the other classes of `S₀`, where `ν`
is relaxed at `cs(Λ)` and unramified at `S`.  It is realised by a class that is relaxed at
`cs(Λ ⊔ L₂)`.

This replaces the Poitou--Tate realisation gate (`IsRealisationInput`, `tatePoitou_h1_realisation`,
`levelK_counting_identity`).  Unlike `IsRealisationInput`, which allows an arbitrary `Λ₀ ⊇ Λ`
with no unramifiedness at `S`, it carries `hL₂`. Without `hL₂` the orthogonality fails against the
characters of `Λ₀` that ramify at `S`.

Proof: expand `S₀` to one place per prime of `K`, then apply `grunwald_escape_relative_v2` with
`(L₁, L₂) := (Λ, L₂)`, `g := ν`, and `h := 0` on the classes of `S`, `h := -ν` on the others.
* `horth₁`: on the other classes the characters of `Λ` vanish by `hnew`.
* `horth₂`: on `S`, `ν` is unramified by `hνT` and the characters of `L₂` are unramified there by
  `hL₂`; on the other classes the datum is `0`.
* `hsplit`: `additive_split_of_abelian_exponent` with `hL₂exp`, `hL₂comm`.
* Involutions: automatic for odd `p`; for `p = 2` use `hKimag`. -/
theorem z_realisation_of_grunwald_v2_own (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (hKimag : p = 2 → ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → c = 1)
    (Λ L₂ : IntermediateField k Ω) [FiniteDimensional k Λ] [IsGalois k Λ]
    [FiniteDimensional k L₂] [IsGalois k L₂] (hKΛ : K ≤ Λ) (hKL₂ : K ≤ L₂)
    (S S₀ : Finset (ValuationSubring Ω)) (hSS₀ : S ⊆ S₀)
    (hS₀fin : ∀ A ∈ S₀, SSGRoute.IsFinPlace k A)
    (hS₀disj : ∀ A ∈ S₀, ∀ B ∈ S₀, SSGRoute.IsConjPlace k A B → A = B)
    (hS₀cov : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (B.valuation (p : Ω) < 1 ∨ SSGRoute.IsRamifiedIn k Λ B ∨ SSGRoute.IsRamifiedIn k L₂ B) →
      ∃ A ∈ S₀, SSGRoute.IsConjPlace k A B)
    (hnew : ∀ A ∈ S₀, A ∉ S → SSGRoute.IsSplitIn k Λ A)
    (hL₂ : ∀ A ∈ S, ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → σ ∈ L₂.fixingSubgroup)
    (hL₂exp : ∀ σ ∈ K.fixingSubgroup, σ ^ p ∈ L₂.fixingSubgroup)
    (hL₂comm : ∀ σ ∈ K.fixingSubgroup, ∀ τ ∈ K.fixingSubgroup,
      σ * τ * σ⁻¹ * τ⁻¹ ∈ L₂.fixingSubgroup)
    (ν : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hν : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, ν (g * h) = ν g + ν h)
    (hνc : SSGRoute.IsLocConstOn K.fixingSubgroup ν)
    (hνS : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → ν σ = 0)
    (hνT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → ν σ = 0) :
    ∃ yt : (Ω ≃ₐ[k] Ω) → ZMod p,
      IsYRealisation p K (Λ ⊔ L₂) S S₀ (fun _ => ν) yt := by
  classical
  -- ## Step 1: the enlarged place set `T`, one place per prime of `K` over `S₀`
  obtain ⟨T, hTfin, hTdisj, hTclos, hTcovK⟩ :=
    zrv2_exists_KConj_cover_closed k Ω K S₀ hS₀fin hS₀disj
  -- ## Step 2: normality of the fixing subgroups
  have hNormK : (K.fixingSubgroup).Normal := by
    rw [← IntermediateField.restrictNormalHom_ker K]; exact MonoidHom.normal_ker _
  have hNormL₂ : (L₂.fixingSubgroup).Normal := by
    rw [← IntermediateField.restrictNormalHom_ker L₂]; exact MonoidHom.normal_ker _
  have hNormΛL : ((Λ ⊔ L₂ : IntermediateField k Ω).fixingSubgroup).Normal := by
    rw [← IntermediateField.restrictNormalHom_ker (Λ ⊔ L₂)]; exact MonoidHom.normal_ker _
  -- ## Step 3: the local correction `h`
  have hh_eq : ∀ A σ, zrv2CorrectionDatum S ν A σ =
      (if ∃ A' ∈ S, IsConjPlace k A' A then (0 : ZMod p) else -ν σ) := fun A σ => rfl
  -- ## Step 4: the hypotheses of `grunwald_escape_relative_v2`
  have hTcov : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (B.valuation (p : Ω) < 1 ∨
        (∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ σ ∉ Λ.fixingSubgroup) ∨
        (∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ σ ∉ L₂.fixingSubgroup)) →
      ∃ A ∈ T, ∃ τ ∈ K.fixingSubgroup, τ • A = B := by
    intro B hBfin hcond
    have hcov : B.valuation (p : Ω) < 1 ∨ SSGRoute.IsRamifiedIn k Λ B ∨
        SSGRoute.IsRamifiedIn k L₂ B := by
      rcases hcond with h | h | h
      · exact Or.inl h
      · obtain ⟨σ, -, hσI, hσnotin⟩ := h
        exact Or.inr (Or.inl ⟨σ, hσI, hσnotin⟩)
      · obtain ⟨σ, -, hσI, hσnotin⟩ := h
        exact Or.inr (Or.inr ⟨σ, hσI, hσnotin⟩)
    obtain ⟨A₀, hA₀, hA₀B⟩ := hS₀cov B hBfin hcov
    obtain ⟨A, hAT, hAB⟩ := hTcovK B hBfin ⟨A₀, hA₀, hA₀B⟩
    exact ⟨A, hAT, hAB⟩
  have hgram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ T, ∀ τ ∈ K.fixingSubgroup, τ • A ≠ B) → ¬ SSGRoute.IsSplitIn k Λ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → ν σ = 0 := by
    intro B hBfin hBT hns σ hσK hσI
    refine hνS B hBfin ?_ hns σ hσK hσI
    intro A' hA'S hA'B
    obtain ⟨A, hAT, τ, hτK, hτA⟩ := hTcovK B hBfin ⟨A', hSS₀ hA'S, hA'B⟩
    exact hBT A hAT τ hτK hτA
  have hh : ∀ A ∈ T, ∀ x ∈ decomp k A ⊓ K.fixingSubgroup,
      ∀ y ∈ decomp k A ⊓ K.fixingSubgroup,
      zrv2CorrectionDatum S ν A (x * y) = zrv2CorrectionDatum S ν A x +
        zrv2CorrectionDatum S ν A y := by
    intro A hAT x hx y hy
    by_cases hSconj : ∃ A' ∈ S, IsConjPlace k A' A
    · have hz0 : ∀ s, zrv2CorrectionDatum S ν A s = 0 := fun s => by
        rw [hh_eq A s, if_pos hSconj]
      rw [hz0 (x * y), hz0 x, hz0 y]
      simp
    · have hz0 : ∀ s, zrv2CorrectionDatum S ν A s = -ν s := fun s => by
        rw [hh_eq A s, if_neg hSconj]
      rw [hz0 (x * y), hz0 x, hz0 y]
      have := hν x (Subgroup.mem_inf.mp hx).2 y (Subgroup.mem_inf.mp hy).2
      rw [this]; abel
  have hhc : ∀ A ∈ T, ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
      ∀ x ∈ U, x ∈ decomp k A ⊓ K.fixingSubgroup → zrv2CorrectionDatum S ν A x = 0 := by
    intro A hAT
    by_cases hSconj : ∃ A' ∈ S, IsConjPlace k A' A
    · refine ⟨⊤, ?_, fun x hx hxl => ?_⟩
      · rw [Subgroup.coe_top]; exact isOpen_univ
      · rw [hh_eq A x, if_pos hSconj]
    · obtain ⟨U, hUopen, hUc⟩ := hνc
      refine ⟨U, hUopen, fun x hxU hxl => ?_⟩
      have hxK : x ∈ K.fixingSubgroup := (Subgroup.mem_inf.mp hxl).2
      have hνx : ν x = 0 := by
        have h1 := hUc 1 K.fixingSubgroup.one_mem x hxU hxK
        rw [one_mul] at h1
        rw [h1, zrv2_additive_one_eq_zero hν]
      rw [hh_eq A x, if_neg hSconj, hνx, neg_zero]
  have horth₁ : ∀ A ∈ T,
      (∀ σ ∈ decomp k A ⊓ K.fixingSubgroup, zrv2CorrectionDatum S ν A σ = 0) ∨
      (∀ χ : (Ω ≃ₐ[k] Ω) → ZMod p,
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
        (∀ σ ∈ Λ.fixingSubgroup, χ σ = 0) →
        ∀ σ ∈ decomp k A ⊓ K.fixingSubgroup, χ σ = 0) ∨
      ((∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ →
          zrv2CorrectionDatum S ν A σ = 0) ∧
        ∀ χ : (Ω ≃ₐ[k] Ω) → ZMod p,
          (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
          (∀ σ ∈ Λ.fixingSubgroup, χ σ = 0) →
          ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → χ σ = 0) := by
    intro A hAT
    by_cases hSconj : ∃ A' ∈ S, IsConjPlace k A' A
    · left
      intro σ hσ
      rw [hh_eq A σ, if_pos hSconj]
    · right; left
      -- `A` lies over a prime of `S₀ ∖ S`, hence is split in `Λ`, so characters of `Λ`
      -- vanish on its decomposition group.
      have hsplitA : SSGRoute.IsSplitIn k Λ A := by
        obtain ⟨A₀, hA₀, hA₀A⟩ := hTclos A hAT
        have hA₀notS : A₀ ∉ S := fun h => hSconj ⟨A₀, h, hA₀A⟩
        obtain ⟨γ, hγ⟩ := hA₀A
        have := (isSplitIn_conj Λ (by
          rw [← IntermediateField.restrictNormalHom_ker Λ]; exact MonoidHom.normal_ker _)
          A₀ γ).mpr (hnew A₀ hA₀ hA₀notS)
        rwa [hγ] at this
      intro χ hχadd hχL1 σ hσ
      exact hχL1 σ (hsplitA (Subgroup.mem_inf.mp hσ).1)
  have horth₂ : ∀ A ∈ T,
      (∀ σ ∈ decomp k A ⊓ K.fixingSubgroup, ν σ + zrv2CorrectionDatum S ν A σ = 0) ∨
      (∀ χ : (Ω ≃ₐ[k] Ω) → ZMod p,
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
        (∀ σ ∈ L₂.fixingSubgroup, χ σ = 0) →
        ∀ σ ∈ decomp k A ⊓ K.fixingSubgroup, χ σ = 0) ∨
      ((∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ →
          ν σ + zrv2CorrectionDatum S ν A σ = 0) ∧
        ∀ χ : (Ω ≃ₐ[k] Ω) → ZMod p,
          (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
          (∀ σ ∈ L₂.fixingSubgroup, χ σ = 0) →
          ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → χ σ = 0) := by
    intro A hAT
    by_cases hSconj : ∃ A' ∈ S, IsConjPlace k A' A
    · right; right
      constructor
      · intro σ hσK hσI
        have hν0 : ν σ = 0 := hνT A (hTfin A hAT) hSconj σ hσK hσI
        rw [hh_eq A σ, if_pos hSconj, hν0, add_zero]
      · intro χ hχadd hχL2 σ hσK hσI
        -- the inertia at a place of `S` is contained in `L₂.fixingSubgroup` by `hL₂`
        obtain ⟨A', hA'S, γ, hγ⟩ := hSconj
        have hmemK : γ⁻¹ * σ * γ ∈ K.fixingSubgroup := by
          simpa using hNormK.conj_mem σ hσK γ⁻¹
        have hI' : SSGRoute.IsInertia k A' (γ⁻¹ * σ * γ) := by
          have h2 : γ * (γ⁻¹ * σ * γ) * γ⁻¹ = σ := by group
          have hthis : SSGRoute.IsInertia k (γ • A') (γ * (γ⁻¹ * σ * γ) * γ⁻¹) := by
            rw [h2, hγ]; exact hσI
          exact (isInertia_conj A' γ (γ⁻¹ * σ * γ)).mp hthis
        have hmemL₂ : γ⁻¹ * σ * γ ∈ L₂.fixingSubgroup := hL₂ A' hA'S _ hmemK hI'
        have h2 : γ * (γ⁻¹ * σ * γ) * γ⁻¹ = σ := by group
        rw [← h2]
        exact hχL2 _ ((conj_mem_iff hNormL₂ γ (γ⁻¹ * σ * γ)).mpr hmemL₂)
    · left
      intro σ hσ
      rw [hh_eq A σ, if_neg hSconj]
      abel
  -- ## Step 4b: the splitting of characters (`Gal(L₂/K)` is abelian of exponent `p`)
  have hsplit : ∀ χ : (Ω ≃ₐ[k] Ω) → ZMod p,
      (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
      (∀ σ ∈ (Λ ⊔ L₂ : IntermediateField k Ω).fixingSubgroup, χ σ = 0) →
      ∃ χ₁ χ₂ : (Ω ≃ₐ[k] Ω) → ZMod p,
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ₁ (x * y) = χ₁ x + χ₁ y) ∧
        (∀ σ ∈ Λ.fixingSubgroup, χ₁ σ = 0) ∧
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ₂ (x * y) = χ₂ x + χ₂ y) ∧
        (∀ σ ∈ L₂.fixingSubgroup, χ₂ σ = 0) ∧
        ∀ σ ∈ K.fixingSubgroup, χ σ = χ₁ σ + χ₂ σ :=
    fun χ hχ hχ0 =>
      zrv2_split_aux p K.fixingSubgroup Λ.fixingSubgroup L₂.fixingSubgroup
        (IntermediateField.fixingSubgroup_le hKL₂) (IntermediateField.fixingSubgroup_le hKΛ)
        hL₂exp hL₂comm χ hχ
        (fun σ hσ => hχ0 σ (by rw [IntermediateField.fixingSubgroup_sup]; exact hσ))
  -- ## Step 5: the Grünwald realisation
  obtain ⟨z, Q, hQfin, hQsplit, hQnotT, hzadd, hzloc, hzpresc, hzunr⟩ :=
    zrv2_escape p k Ω K ζ hζ hζK hKimag Λ L₂ hKΛ hKL₂ T hTfin hTdisj hTcov
      ν hν hνc hgram (zrv2CorrectionDatum S ν) hh hhc horth₁ horth₂ hsplit
  refine ⟨z, ?_⟩
  -- ## Step 6: `z` is a realisation of the prescribed datum
  have hres : ∀ g ∈ K.fixingSubgroup, res k K g = 1 := by
    intro g hg
    rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker K]
    exact hg
  refine ⟨?_, hzloc, ?_, ?_, ?_, ?_⟩
  · -- clause (1): `z` is a cocycle
    intro g hg h' hh'
    rw [hres g hg, one_smul]
    exact hzadd g hg h' hh'
  · -- clause (3): the prescribed values at the classes of `S`
    intro B hBconj
    obtain ⟨A', hA'S, hA'B⟩ := hBconj
    have hBfin : SSGRoute.IsFinPlace k B := by
      obtain ⟨γ, hγ⟩ := hA'B
      rw [← hγ]
      exact (isFinPlace_smul_iff A' γ).mpr (hS₀fin A' (hSS₀ hA'S))
    obtain ⟨A, hAT, τ, hτK, hτA⟩ := hTcovK B hBfin ⟨A', hSS₀ hA'S, hA'B⟩
    have hAconjS : ∃ A'' ∈ S, IsConjPlace k A'' A :=
      ⟨A', hA'S, isConjPlace_trans hA'B
        (isConjPlace_symm (ZConstruction.kConj_isConjPlace ⟨τ, hτK, hτA⟩))⟩
    have hhA : ∀ s, zrv2CorrectionDatum S ν A s = 0 := fun s => by
      rw [hh_eq A s, if_pos hAconjS]
    refine ⟨0, fun σ hσ => ?_⟩
    show z σ - ν σ = res k K σ • (0 : ZMod p) - 0
    have hσK : σ ∈ K.fixingSubgroup := (Subgroup.mem_inf.mp hσ).2
    have hσD : σ ∈ decomp k B := (Subgroup.mem_inf.mp hσ).1
    have hσ'K : τ⁻¹ * σ * τ ∈ K.fixingSubgroup := by
      simpa using hNormK.conj_mem σ hσK τ⁻¹
    have hσ' : τ⁻¹ * σ * τ ∈ decomp k A ⊓ K.fixingSubgroup :=
      Subgroup.mem_inf.mpr ⟨zrv2_inv_conj_mem_decomp hτA hσD, hσ'K⟩
    have hzval : z (τ⁻¹ * σ * τ) = ν (τ⁻¹ * σ * τ) := by
      rw [hzpresc A hAT _ hσ', hhA (τ⁻¹ * σ * τ), add_zero]
    have hconj : τ * (τ⁻¹ * σ * τ) * τ⁻¹ = σ := by group
    have hzσ : z σ = z (τ⁻¹ * σ * τ) := by
      conv_lhs => rw [← hconj]
      exact zrv2_additive_conj_eq hzadd hσ'K hτK
    have hνσ : ν σ = ν (τ⁻¹ * σ * τ) := by
      conv_lhs => rw [← hconj]
      exact zrv2_additive_conj_eq hν hσ'K hτK
    rw [hzσ, hνσ, hzval]
    simp
  · -- clause (4): vanishing at the classes of `S₀ ∖ S`
    intro B hBfin hBsupp hBnotS σ hσK hσD
    obtain ⟨A, hAT, τ, hτK, hτA⟩ := hTcovK B hBfin hBsupp
    have hAnotS : ¬ ∃ A'' ∈ S, IsConjPlace k A'' A := by
      rintro ⟨A'', hA''S, hA''A⟩
      exact hBnotS A'' hA''S (isConjPlace_trans hA''A
        (ZConstruction.kConj_isConjPlace ⟨τ, hτK, hτA⟩))
    have hσ'K : τ⁻¹ * σ * τ ∈ K.fixingSubgroup := by
      simpa using hNormK.conj_mem σ hσK τ⁻¹
    have hσ' : τ⁻¹ * σ * τ ∈ decomp k A ⊓ K.fixingSubgroup :=
      Subgroup.mem_inf.mpr ⟨zrv2_inv_conj_mem_decomp hτA hσD, hσ'K⟩
    have hzval : z (τ⁻¹ * σ * τ) = 0 := by
      rw [hzpresc A hAT _ hσ',
        show zrv2CorrectionDatum S ν A (τ⁻¹ * σ * τ) = -ν (τ⁻¹ * σ * τ) from by
          rw [hh_eq A (τ⁻¹ * σ * τ), if_neg hAnotS],
        add_neg_cancel]
    have hconj : τ * (τ⁻¹ * σ * τ) * τ⁻¹ = σ := by group
    have hzσ : z σ = z (τ⁻¹ * σ * τ) := by
      conv_lhs => rw [← hconj]
      exact zrv2_additive_conj_eq hzadd hσ'K hτK
    rw [hzσ]; exact hzval
  · -- clause (5): unramifiedness outside `S₀` at the places not split in `Λ ⊔ L₂`
    intro B hBfin hBnotS₀ hnotsplit σ hσK hσI
    refine hzunr B hBfin ?_ ?_ σ hσK hσI
    · intro A hAT τ hτK hτA
      obtain ⟨A₀, hA₀, hA₀A⟩ := hTclos A hAT
      exact hBnotS₀ A₀ hA₀ (isConjPlace_trans hA₀A
        (ZConstruction.kConj_isConjPlace ⟨τ, hτK, hτA⟩))
    · intro τ hτK hτQ
      have hsplitB : SSGRoute.IsSplitIn k (Λ ⊔ L₂) B := by
        have := (isSplitIn_conj (Λ ⊔ L₂) hNormΛL Q τ).mpr hQsplit
        rwa [hτQ] at this
      exact hnotsplit hsplitB
  · -- clause (6): the involutions are killed
    intro c hcK hc2
    by_cases hp2 : p = 2
    · rw [hKimag hp2 c hcK hc2]
      exact zrv2_additive_one_eq_zero hzadd
    · have h2ne : (2 : ZMod p) ≠ 0 := by
        intro h
        have h' : ((2 : ℕ) : ZMod p) = 0 := h
        rw [ZMod.natCast_eq_zero_iff] at h'
        rcases (Nat.dvd_prime Nat.prime_two).mp h' with h1 | h1
        · exact (Fact.out : p.Prime).ne_one h1
        · exact hp2 h1
      have hmul : z (c * c) = z c + z c := hzadd c hcK c hcK
      have hcc : c * c = 1 := by rw [← pow_two]; exact hc2
      rw [hcc, zrv2_additive_one_eq_zero hzadd] at hmul
      have hzero : (2 : ZMod p) * z c = 0 := by rw [two_mul]; exact hmul.symm
      exact (mul_eq_zero.mp hzero).resolve_left h2ne

end Work.SSGRoute
