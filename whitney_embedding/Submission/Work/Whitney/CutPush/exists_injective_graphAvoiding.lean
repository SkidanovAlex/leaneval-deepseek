import Mathlib

/-!
# A graph avoiding two given planes: the genericity half of the flat model

`Work.Whitney.CutPush.companionDatumExists`'s flat-model step needs a *linear* general-position
statement: given the two decompositions of `E ≅ ℝ^{2n}` cut out by the two crossings
(`E = T_{p₁} ⊕ T_{p₂} = T_{q₁} ⊕ T_{q₂}`, all four summands `n`-dimensional), find an `n`-plane `K`
transverse to all four.  Such a `K` is the graph of an injective `A : L₁ → L₂`, and the corresponding
projection `π` with `ker π = K` (an isomorphism `E → E/K ≅ ℝ^n`, whose existence is
`exists_continuousLinearEquiv_of_base_projection`) is the `Φ` of the flat model.

This file proves the general-position statement by a **quotient recursion** (no Grassmannian, no
measure theory): a finite family of proper subspaces of a finite-dimensional real vector space has a
common transverse complement, of the exact dimension `finrank E - m` when all members have dimension
`≤ m`.  The recursion picks `v` outside the union of the (images of the) subspaces
(`Submodule.exists_forall_notMem_of_forall_ne_top`), quotients by `⟨v⟩` and iterates; the lifted plane
is `K̄.comap π`.  The base case is `K = ⊥`.

Main results:

* `finrank_map_add_finrank_inf_ker` — rank-nullity for a submodule;
* `exists_transverse_of_finrank_le` — the quotient recursion;
* `exists_injective_graphAvoiding` — the reviewed statement (its coordinate half is
  `graphSubmodule_compl_avoiding` in `CutPush/companionDatumExists.lean`).
-/

open Submodule

namespace Work.Whitney.CutPush

variable {E E' : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup E'] [Module ℝ E']
  [FiniteDimensional ℝ E]

/-- **Rank-nullity for a submodule.**  `finrank p = finrank (p.map f) + finrank (p ⊓ ker f)`. -/
theorem finrank_map_add_finrank_inf_ker (f : E →ₗ[ℝ] E') (p : Submodule ℝ E) :
    Module.finrank ℝ ↥p = Module.finrank ℝ ↥(p.map f) + Module.finrank ℝ ↥(p ⊓ f.ker) := by
  have h := LinearMap.finrank_range_add_finrank_ker (f.comp p.subtype)
  have hrange : (f.comp p.subtype).range = p.map f := by
    ext x
    simp [LinearMap.mem_range, Submodule.mem_map]
  have hker : Module.finrank ℝ ↥((f.comp p.subtype).ker) = Module.finrank ℝ ↥(p ⊓ f.ker) := by
    have hinj : Function.Injective (p.subtype.comp ((f.comp p.subtype).ker).subtype) :=
      p.subtype_injective.comp Subtype.val_injective
    have h2 := LinearMap.finrank_range_of_inj (f := p.subtype.comp
      ((f.comp p.subtype).ker).subtype) hinj
    have h3 : (p.subtype.comp ((f.comp p.subtype).ker).subtype).range = p ⊓ f.ker := by
      ext x
      simp [LinearMap.mem_range, Submodule.mem_inf, and_comm]
    rw [← h2, h3]
  rw [hrange, hker] at h
  exact h.symm

/-- **A finite family of proper subspaces has a common transverse complement.**  If `m ≤ finrank E`
and every `L ∈ S` has `finrank L ≤ m`, then there is a subspace `K` of dimension `finrank E - m`
meeting every `L ∈ S` trivially. -/
theorem exists_transverse_of_finrank_le : ∀ (t : ℕ) {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] (m : ℕ) (S : Finset (Submodule ℝ E)), S.Nonempty →
    Module.finrank ℝ E - m = t → (∀ L ∈ S, Module.finrank ℝ ↥L ≤ m) →
    ∃ K : Submodule ℝ E, Module.finrank ℝ ↥K = Module.finrank ℝ E - m ∧
      ∀ L ∈ S, K ⊓ L = ⊥ := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro E _ _ _ m S hne ht hS
    by_cases ht0 : t = 0
    · refine ⟨⊥, ?_, by intro L _; simp⟩
      rw [finrank_bot, ht, ht0]
    · have hlt : m < Module.finrank ℝ E := by omega
      have hproper : ∀ L ∈ S, L ≠ ⊤ := by
        intro L hL htop
        have hLf : Module.finrank ℝ ↥L = Module.finrank ℝ E := by rw [htop]; simp
        have := hS L hL
        omega
      obtain ⟨v, hv⟩ := Submodule.exists_forall_notMem_of_forall_ne_top
        (fun L : S => (L : Submodule ℝ E)) (fun L => hproper L L.2)
      have hv0 : v ≠ 0 := by
        obtain ⟨L, hL⟩ := hne
        intro h0
        exact hv ⟨L, hL⟩ (h0 ▸ L.zero_mem)
      set N : Submodule ℝ E := Submodule.span ℝ ({v} : Set E) with hN
      have hNfin : Module.finrank ℝ ↥N = 1 := by
        rw [hN]; exact finrank_span_singleton hv0
      set π : E →ₗ[ℝ] E ⧸ N := N.mkQ with hπ
      have hkerπ : π.ker = N := by rw [hπ]; exact Submodule.ker_mkQ N
      have hq : Module.finrank ℝ (E ⧸ N) = Module.finrank ℝ E - 1 := by
        have h1 := Submodule.finrank_quotient_add_finrank N
        rw [hNfin] at h1
        omega
      set S' : Finset (Submodule ℝ (E ⧸ N)) := S.image (fun L => L.map π) with hS'
      have hneS' : S'.Nonempty := by
        obtain ⟨L, hL⟩ := hne
        exact ⟨L.map π, by rw [hS']; exact Finset.mem_image.mpr ⟨L, hL, rfl⟩⟩
      have hfinS' : ∀ L' ∈ S', Module.finrank ℝ ↥L' ≤ m := by
        intro L' hL'
        rw [hS'] at hL'
        obtain ⟨L, hL, rfl⟩ := Finset.mem_image.mp hL'
        exact le_trans (Submodule.finrank_map_le π L) (hS L hL)
      have ht' : Module.finrank ℝ (E ⧸ N) - m = t - 1 := by omega
      obtain ⟨Kbar, hKbarfin, hKbar⟩ := ih (t - 1) (by omega) m S' hneS' ht' hfinS'
      have hsurj : Function.Surjective π := by rw [hπ]; exact Submodule.mkQ_surjective N
      refine ⟨Kbar.comap π, ?_, ?_⟩
      · have hmap : (Kbar.comap π).map π = Kbar := by
          rw [Submodule.map_comap_eq, LinearMap.range_eq_top.mpr hsurj, top_inf_eq]
        have hle : N ≤ Kbar.comap π := by
          intro y hy
          have hyk : y ∈ π.ker := by rw [hkerπ]; exact hy
          show π y ∈ Kbar
          rw [LinearMap.mem_ker.mp hyk]
          exact Kbar.zero_mem
        have hinf : Kbar.comap π ⊓ N = N := inf_eq_right.mpr hle
        have h := finrank_map_add_finrank_inf_ker π (Kbar.comap π)
        rw [hmap, hkerπ, hinf, hKbarfin, hq, hNfin] at h
        omega
      · intro L hL
        have hNL : N ⊓ L = ⊥ := by
          rw [eq_bot_iff]
          intro y hy
          obtain ⟨hyN, hyL⟩ := Submodule.mem_inf.mp hy
          rw [hN] at hyN
          obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hyN
          subst hc
          by_cases hc0 : c = 0
          · simp [hc0]
          · exfalso
            have : v ∈ L := by
              have := L.smul_mem c⁻¹ hyL
              rwa [smul_smul, inv_mul_cancel₀ hc0, one_smul] at this
            exact hv ⟨L, hL⟩ this
        rw [Submodule.eq_bot_iff]
        intro x hx
        obtain ⟨hxK, hxL⟩ := Submodule.mem_inf.mp hx
        have h3 : π x ∈ Kbar ⊓ L.map π :=
          ⟨hxK, ⟨x, hxL, rfl⟩⟩
        rw [hKbar (L.map π)
          (by rw [hS']; exact Finset.mem_image.mpr ⟨L, hL, rfl⟩)] at h3
        have hxN : x ∈ N := by
          rw [← hkerπ]
          exact LinearMap.mem_ker.mpr (by simpa using h3)
        have hmem : x ∈ (⊥ : Submodule ℝ E) := hNL ▸ Submodule.mem_inf.mpr ⟨hxN, hxL⟩
        simpa using hmem



/-- **Generic position of two complementary splittings.**  Given two decompositions of a
finite-dimensional real vector space into complementary `n`-planes, there is an injective linear
`A : L₁ → L₂` whose graph misses both `L₃` and `L₄`. -/
theorem exists_injective_graphAvoiding {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    [Module.Finite ℝ E] (L₁ L₂ L₃ L₄ : Submodule ℝ E)
    (h₁₂ : IsCompl L₁ L₂) (h₃₄ : IsCompl L₃ L₄)
    (h1 : Module.finrank ℝ ↥L₁ = n) (h2 : Module.finrank ℝ ↥L₂ = n)
    (h3 : Module.finrank ℝ ↥L₃ = n) (h4 : Module.finrank ℝ ↥L₄ = n) :
    ∃ A : L₁ →ₗ[ℝ] L₂, Function.Injective A ∧
      LinearMap.range (L₁.subtype + L₂.subtype.comp A) ⊓ L₃ = ⊥ ∧
      LinearMap.range (L₁.subtype + L₂.subtype.comp A) ⊓ L₄ = ⊥ := by
  classical
  have hdE : Module.finrank ℝ E = 2 * n := by
    have h := Submodule.finrank_add_eq_of_isCompl h₁₂
    omega
  have hSfin : ∀ L ∈ ({L₁, L₂, L₃, L₄} : Finset (Submodule ℝ E)),
      Module.finrank ℝ ↥L ≤ n := by
    intro L hL
    simp only [Finset.mem_insert, Finset.mem_singleton] at hL
    rcases hL with rfl | rfl | rfl | rfl <;> simp [h1, h2, h3, h4]
  obtain ⟨K, hKfin, hKtr⟩ := exists_transverse_of_finrank_le (Module.finrank ℝ E - n) n
    ({L₁, L₂, L₃, L₄} : Finset (Submodule ℝ E)) ⟨L₁, by simp⟩ rfl hSfin
  have hKn : Module.finrank ℝ ↥K = n := by omega
  have hK₁ : K ⊓ L₁ = ⊥ := hKtr L₁ (by simp)
  have hK₂ : K ⊓ L₂ = ⊥ := hKtr L₂ (by simp)
  have hK₃ : K ⊓ L₃ = ⊥ := hKtr L₃ (by simp)
  have hK₄ : K ⊓ L₄ = ⊥ := hKtr L₄ (by simp)
  -- the two projections of the splitting `E = L₁ ⊕ L₂`
  set e := Submodule.prodEquivOfIsCompl L₁ L₂ h₁₂ with he
  set π₁ : E →ₗ[ℝ] L₁ := (LinearMap.fst ℝ L₁ L₂).comp e.symm.toLinearMap with hπ₁
  set π₂ : E →ₗ[ℝ] L₂ := (LinearMap.snd ℝ L₁ L₂).comp e.symm.toLinearMap with hπ₂
  have hsum : ∀ x : E, ((π₁ x : L₁) : E) + ((π₂ x : L₂) : E) = x := by
    intro x
    have h1' : e (e.symm x) = x := e.apply_symm_apply x
    have h2' : e.symm x = (π₁ x, π₂ x) := rfl
    rw [h2'] at h1'
    have key : e (π₁ x, π₂ x) = ((π₁ x : L₁) : E) + ((π₂ x : L₂) : E) := by
      rw [he, Submodule.coe_prodEquivOfIsCompl']
    rw [← key]
    exact h1'
  have hker₁ : π₁.ker = L₂ := by
    ext x
    exact Submodule.prodEquivOfIsCompl_symm_apply_fst_eq_zero L₁ L₂ h₁₂
  have hker₂ : π₂.ker = L₁ := by
    ext x
    exact Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero L₁ L₂ h₁₂
  have hκinj : Function.Injective (π₁.comp K.subtype) := by
    intro u w huw
    have hzero : (π₁.comp K.subtype) (u - w) = 0 := by rw [map_sub, huw, sub_self]
    have hmem : ((u - w : K) : E) ∈ L₂ := by
      rw [← hker₁]
      exact LinearMap.mem_ker.mpr hzero
    have hbot : ((u - w : K) : E) = 0 :=
      (Submodule.eq_bot_iff (K ⊓ L₂)).mp hK₂ _ ⟨(u - w).2, hmem⟩
    exact sub_eq_zero.mp (Subtype.ext hbot)
  set e₁ : K ≃ₗ[ℝ] L₁ :=
    LinearMap.linearEquivOfInjective (π₁.comp K.subtype) hκinj (by rw [hKn, h1]) with he₁
  set A : L₁ →ₗ[ℝ] L₂ := π₂.comp (K.subtype.comp e₁.symm.toLinearMap) with hA
  have hAapply : ∀ v : L₁, A v = π₂ ((e₁.symm v : K) : E) := by
    intro v; rw [hA]; rfl
  have hAinj : Function.Injective A := by
    intro u w huw
    have h0 : A (u - w) = 0 := by rw [map_sub, huw, sub_self]
    set z : K := e₁.symm (u - w) with hz
    have h0' : π₂ (z : E) = 0 := by
      have hz1 : A (u - w) = π₂ (z : E) := by rw [hAapply (u - w), hz]
      rw [← hz1]
      exact h0
    have hmem : (z : E) ∈ K ⊓ L₁ :=
      ⟨z.2, by rw [← hker₂]; exact LinearMap.mem_ker.mpr h0'⟩
    have hz0 : (z : E) = 0 := (Submodule.eq_bot_iff (K ⊓ L₁)).mp hK₁ z hmem
    have hzz : z = 0 := Subtype.ext hz0
    have hzw : e₁.symm (u - w) = 0 := by rw [← hz]; exact hzz
    have hlast := congrArg e₁ hzw
    exact sub_eq_zero.mp (by simpa using hlast)


  have hrange : LinearMap.range (L₁.subtype + L₂.subtype.comp A) = K := by
    refine le_antisymm ?_ ?_
    · rintro x ⟨v, rfl⟩
      have hcalc : (L₁.subtype + L₂.subtype.comp A) v = ((e₁.symm v : K) : E) := by
        have hv' : ((π₁ ((e₁.symm v : K) : E) : L₁) : E) = ((v : L₁) : E) :=
          congrArg (fun t : L₁ => (t : E)) (e₁.apply_symm_apply v)
        rw [LinearMap.add_apply, LinearMap.comp_apply, hAapply v]
        conv_rhs => rw [← hsum ((e₁.symm v : K) : E)]
        rw [hv']
        rfl
      rw [hcalc]
      exact (e₁.symm v).2
    · intro x hxK
      set y : K := ⟨x, hxK⟩ with hy
      refine ⟨π₁ y, ?_⟩
      have hπy : (π₁ (y : E) : L₁) = e₁ y := rfl
      have h3 : e₁.symm (π₁ y) = y := by
        rw [hπy]
        exact e₁.symm_apply_apply y
      have hcalc : (L₁.subtype + L₂.subtype.comp A) (π₁ y) = x := by
        have hthis : (L₁.subtype + L₂.subtype.comp A) (π₁ y)
            = L₁.subtype (π₁ y) + L₂.subtype (A (π₁ y)) := rfl
        have h2' : A (π₁ y) = π₂ y := by
          rw [hAapply (π₁ y), h3]
        rw [hthis, h2']
        exact hsum y
      rw [hcalc]
  exact ⟨A, hAinj, by rw [hrange]; exact hK₃, by rw [hrange]; exact hK₄⟩

