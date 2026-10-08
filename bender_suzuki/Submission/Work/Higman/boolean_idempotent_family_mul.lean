import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The Boolean idempotent family lemma

Let `V` be a finite `𝔽₂`-vector space and `ξ` an automorphism permuting the nonzero vectors
transitively (so `V` is irreducible under `ξ` and `ξ` is a Singer cycle).
If `(σ i)` is a family of idempotent endomorphisms of `V` which is additively closed and
`ξ`-stable, then every `σ i` is `0` or the identity.

The proof is elementary.  Writing `F` for the range of `σ` (a submodule of `End V` all of whose
elements are idempotents), we count the set of pairs `(g, w)` with `g ∈ F`, `w ∈ V`, `g w = w`
in two ways.  Counting over `g` gives `∑ g, 2 ^ finrank (range g)`, which is odd; counting over
`w` gives `2 ^ m + ∑_{w ≠ 0} |{g : g w = w}|`.  Oddness singles out a nonzero `w₀` whose fibre in
`F` has odd cardinality; that fibre is a coset of `ker (F → V, g ↦ g w₀)`, whose cardinality is a
power of two, so this kernel is trivial.  Transporting along the `ξ`-orbit of `w₀` shows that
every nonzero `g ∈ F` is injective, and an injective idempotent is the identity.
-/

namespace Work.Higman

open LinearMap

/-! ## Elementary auxiliary facts -/

private lemma zm2_add_self {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (x : V) :
    x + x = 0 := by
  have h : (2 : ZMod 2) • x = x + x := two_smul (ZMod 2) x
  rw [show (2 : ZMod 2) = 0 by decide, zero_smul] at h
  exact h.symm

private lemma conj_cancel_symm {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ξ : V ≃ₗ[ZMod 2] V) (f : V →ₗ[ZMod 2] V) :
    ξ.symm.toLinearMap * (ξ.toLinearMap * f * ξ.symm.toLinearMap) * ξ.toLinearMap = f := by
  ext v
  simp [Module.End.mul_eq_comp]

private lemma conj_cancel {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ξ : V ≃ₗ[ZMod 2] V) (f : V →ₗ[ZMod 2] V) :
    ξ.toLinearMap * (ξ.symm.toLinearMap * f * ξ.toLinearMap) * ξ.symm.toLinearMap = f := by
  ext v
  simp [Module.End.mul_eq_comp]

private lemma mem_bot_zmod {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] {x : M} :
    x ∈ (⊥ : Submodule (ZMod 2) M) ↔ x = 0 := Submodule.mem_bot (ZMod 2)

/-- The linear map `F → V`, `g ↦ g w`. -/
private abbrev psiF {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (F : Submodule (ZMod 2) (V →ₗ[ZMod 2] V)) (w : V) : F →ₗ[ZMod 2] V :=
  { toFun := fun g => g.1 w
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

/-- Transitivity on nonzero vectors implies irreducibility: a nonzero `ξ`-invariant subspace
is everything. -/
private lemma eq_top_of_invariant {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ξ : V ≃ₗ[ZMod 2] V)
    (htrans : ∀ a b : V, a ≠ 0 → b ≠ 0 → ∃ k : ℕ, (ξ ^ k) a = b)
    {W : Submodule (ZMod 2) V} (hW : ∀ v ∈ W, ξ v ∈ W) (hne : W ≠ ⊥) : W = ⊤ := by
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hgen : ∀ n : ℕ, (ξ ^ n) w ∈ W := by
    intro n
    induction n with
    | zero => simpa using hwW
    | succ n ih =>
        rw [pow_succ', LinearEquiv.mul_apply]
        exact hW _ ih
  rw [Submodule.eq_top_iff']
  intro b
  by_cases hb : b = 0
  · rw [hb]; exact W.zero_mem
  · obtain ⟨k, hk⟩ := htrans w b hw0 hb
    rw [← hk]
    exact hgen k

/-- For an idempotent endomorphism, the number of fixed points is `2 ^ finrank (range g)`. -/
private lemma card_fixed {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (g : V →ₗ[ZMod 2] V) (hg : IsIdempotentElem g) :
    Nat.card {w : V // g w = w} = 2 ^ Module.finrank (ZMod 2) (LinearMap.range g) := by
  haveI : Finite ↥(LinearMap.range g) := inferInstance
  haveI : Module.Finite (ZMod 2) ↥(LinearMap.range g) := Module.Finite.of_finite
  rw [Nat.card_congr
    (Equiv.subtypeEquivRight (fun w => (LinearMap.IsIdempotentElem.mem_range_iff hg).symm))]
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥(LinearMap.range g)), Nat.card_zmod]

private lemma filter_card_eq {α : Type*} [Fintype α] (q : α → Prop) [DecidablePred q] :
    (Finset.univ.filter q).card = Nat.card {a : α // q a} := by
  classical
  have h1 : (Finset.univ.filter q).card = Fintype.card ↥(Finset.univ.filter q) :=
    (Fintype.card_coe _).symm
  have h2 : Fintype.card ↥(Finset.univ.filter q) = Fintype.card {a : α // q a} :=
    Fintype.card_congr (Equiv.subtypeEquivRight
      (p := fun a => a ∈ Finset.univ.filter q) (q := q) (fun a => by simp))
  have h3 : Fintype.card {a : α // q a} = Nat.card {a : α // q a} :=
    Nat.card_eq_fintype_card.symm
  rw [h1, h2, h3]

private lemma exists_odd_of_odd_sum {ι : Type*} {s : Finset ι} {f : ι → ℕ}
    (h : Odd (s.sum f)) : ∃ i ∈ s, Odd (f i) := by
  by_contra hc
  push Not at hc
  exact (Nat.not_odd_iff_even.mpr
    (Finset.even_sum f (fun i hi => Nat.not_odd_iff_even.mp (hc i hi)))) h

/-- A nonempty fibre of a linear map has the cardinality of the kernel. -/
private lemma card_fiber_eq_card_ker {A B : Type*} [AddCommGroup A] [Module (ZMod 2) A]
    [Fintype A] [AddCommGroup B] [Module (ZMod 2) B]
    (φ : A →ₗ[ZMod 2] B) {m : B} {a₀ : A} (h : φ a₀ = m) :
    Nat.card {a : A // φ a = m} = Nat.card ↥(LinearMap.ker φ) := by
  refine Nat.card_congr (Equiv.ofBijective (fun k : ↥(LinearMap.ker φ) =>
    (⟨a₀ + k.1, ?_⟩ : {a : A // φ a = m})) ⟨?_, ?_⟩).symm
  · show φ (a₀ + k.1) = m
    rw [map_add, h, k.2, add_zero]
  · intro x y hxy
    exact Subtype.ext (add_left_cancel (congr_arg Subtype.val hxy))
  · intro b
    refine ⟨⟨b.1 + a₀, ?_⟩, Subtype.ext ?_⟩
    · show φ (b.1 + a₀) = 0
      rw [map_add, b.2, h]
      exact zm2_add_self m
    · show a₀ + (b.1 + a₀) = b.1
      rw [show a₀ + (b.1 + a₀) = (a₀ + a₀) + b.1 from by abel, zm2_add_self, zero_add]

/-! ## The main lemma -/

theorem boolean_idempotent_family_univ {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ξ : V ≃ₗ[ZMod 2] V)
    (htrans : ∀ a b : V, a ≠ 0 → b ≠ 0 → ∃ k : ℕ, (ξ ^ k) a = b)
    {ι : Type*} [Fintype ι] (σ : ι → V →ₗ[ZMod 2] V)
    (hidem : ∀ i, (σ i).comp (σ i) = σ i)
    (hadd : ∀ i j, ∃ k, σ k = σ i + σ j)
    (hinv : ∃ τ : ι ≃ ι, ∀ i v, σ (τ i) (ξ v) = ξ (σ i v)) :
    ∀ i, σ i = 0 ∨ σ i = LinearMap.id := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact fun i => (hι.false i).elim
  obtain ⟨τ, hτ⟩ := hinv
  haveI : Fintype V := Fintype.ofFinite V
  haveI hEndFin : Finite (V →ₗ[ZMod 2] V) :=
    Finite.of_injective (fun f : V →ₗ[ZMod 2] V => (f : V → V))
      (fun a b h => LinearMap.ext (fun v => congr_fun h v))
  haveI hEndFintype : Fintype (V →ₗ[ZMod 2] V) := Fintype.ofFinite _
  -- ## The range of `σ` is a submodule of `End V` consisting of idempotents.
  have hzero : (0 : V →ₗ[ZMod 2] V) ∈ Set.range σ := by
    obtain ⟨i⟩ := hι
    obtain ⟨k, hk⟩ := hadd i i
    refine ⟨k, ?_⟩
    rw [hk]
    ext v
    simpa using zm2_add_self (σ i v)
  let F : Submodule (ZMod 2) (V →ₗ[ZMod 2] V) :=
    { carrier := Set.range σ
      zero_mem' := hzero
      add_mem' := by
        rintro a b ⟨i, rfl⟩ ⟨j, rfl⟩
        obtain ⟨k, hk⟩ := hadd i j
        exact ⟨k, hk⟩
      smul_mem' := by
        rintro c x ⟨i, rfl⟩
        have hc : c = 0 ∨ c = 1 := by decide +revert
        rcases hc with hc | hc
        · rw [hc, zero_smul]; exact hzero
        · rw [hc, one_smul]; exact ⟨i, rfl⟩ }
  haveI hFintype : Fintype ↥F := inferInstance
  haveI hFiniteF : Finite ↥F := inferInstance
  have hFidem : ∀ g ∈ F, IsIdempotentElem g := by
    rintro g ⟨i, rfl⟩
    rw [isIdempotentElem_iff, Module.End.mul_eq_comp]
    exact hidem i
  -- ## `F` is stable under conjugation by `ξ` and by `ξ⁻¹`.
  have hconj_eq : ∀ i, ξ.toLinearMap * (σ i) * ξ.symm.toLinearMap = σ (τ i) := by
    intro i
    have h1 : (σ (τ i)).comp ξ.toLinearMap = ξ.toLinearMap.comp (σ i) := by
      ext v; exact hτ i v
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp]
    ext v
    have h := LinearMap.congr_fun h1 (ξ.symm v)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h
    exact h.symm
  have hFconj : ∀ g ∈ F, ξ.toLinearMap * g * ξ.symm.toLinearMap ∈ F := by
    rintro g ⟨i, rfl⟩
    exact ⟨τ i, (hconj_eq i).symm⟩
  have hFconj_inv : ∀ g ∈ F, ξ.symm.toLinearMap * g * ξ.toLinearMap ∈ F := by
    rintro g ⟨j, rfl⟩
    obtain ⟨i, rfl⟩ := τ.surjective j
    refine ⟨i, ?_⟩
    rw [← hconj_eq i, conj_cancel_symm]
  -- ## Triviality of `ker (psiF F w)` is stable under `ξ`.
  have hker_step : ∀ w : V, LinearMap.ker (psiF F w) = ⊥ → LinearMap.ker (psiF F (ξ w)) = ⊥ := by
    intro w hw
    rw [Submodule.eq_bot_iff]
    intro g hg
    have hgv : g.1 (ξ w) = 0 := hg
    have hg'in : ξ.symm.toLinearMap * g.1 * ξ.toLinearMap ∈ F := hFconj_inv g.1 g.2
    have hmem : (⟨ξ.symm.toLinearMap * g.1 * ξ.toLinearMap, hg'in⟩ : F)
        ∈ LinearMap.ker (psiF F w) := by
      rw [LinearMap.mem_ker]
      show (ξ.symm.toLinearMap * g.1 * ξ.toLinearMap) w = 0
      simp [Module.End.mul_eq_comp, hgv]
    rw [hw] at hmem
    have hz : (⟨ξ.symm.toLinearMap * g.1 * ξ.toLinearMap, hg'in⟩ : F) = 0 :=
      mem_bot_zmod.mp hmem
    have hz' : ξ.symm.toLinearMap * g.1 * ξ.toLinearMap = 0 := by
      have := congr_arg Subtype.val hz
      simpa using this
    have hg0 : g.1 = 0 := by
      have := congr_arg (fun f : V →ₗ[ZMod 2] V => ξ.toLinearMap * f * ξ.symm.toLinearMap) hz'
      rw [conj_cancel] at this
      simpa using this
    exact Subtype.ext hg0
  -- ## The double count.
  set ff : V → ℕ := fun w => (Finset.univ.filter (fun g : F => psiF F w g = w)).card with hffdef
  have hffval : ∀ w : V, ff w = (Finset.univ.filter (fun g : F => psiF F w g = w)).card :=
    fun w => by rw [hffdef]
  set T : ℕ := ∑ g : F, (Finset.univ.filter (fun w : V => (g : V →ₗ[ZMod 2] V) w = w)).card
    with hTdef
  have hcardF : Fintype.card F = 2 ^ Module.finrank (ZMod 2) F := by
    haveI : Module.Finite (ZMod 2) ↥F := Module.Finite.of_finite
    rw [← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥F),
      Nat.card_zmod]
  have hTfib : T = ∑ w : V, ff w := by
    have h1 : T = ∑ g : F, ∑ w : V,
        (if (g : V →ₗ[ZMod 2] V) w = w then (1 : ℕ) else 0) := by
      rw [hTdef]
      exact Finset.sum_congr rfl (fun g _ => Finset.card_filter _ _)
    have h2 : (∑ g : F, ∑ w : V, (if (g : V →ₗ[ZMod 2] V) w = w then (1 : ℕ) else 0))
        = ∑ w : V, ∑ g : F, (if (g : V →ₗ[ZMod 2] V) w = w then (1 : ℕ) else 0) :=
      Finset.sum_comm
    have h3 : (∑ w : V, ∑ g : F, (if (g : V →ₗ[ZMod 2] V) w = w then (1 : ℕ) else 0))
        = ∑ w : V, (Finset.univ.filter (fun g : F => psiF F w g = w)).card := by
      refine Finset.sum_congr rfl (fun w _ => ?_)
      rw [Finset.card_filter]
      exact Finset.sum_congr rfl (fun g _ => by simp)
    have h4 : (∑ w : V, (Finset.univ.filter (fun g : F => psiF F w g = w)).card)
        = ∑ w : V, ff w :=
      Finset.sum_congr rfl (fun w _ => (hffval w).symm)
    rw [h1, h2, h3, h4]
  -- ## `T` is odd.
  have hTodd : Odd T := by
    have hstep : T = ∑ g : F,
        2 ^ Module.finrank (ZMod 2) (LinearMap.range (g : V →ₗ[ZMod 2] V)) := by
      rw [hTdef]
      refine Finset.sum_congr rfl (fun g _ => ?_)
      rw [filter_card_eq (fun w : V => (g : V →ₗ[ZMod 2] V) w = w)]
      exact card_fixed (g : V →ₗ[ZMod 2] V) (hFidem g g.2)
    rw [hstep]
    have hsplit := Finset.add_sum_erase (Finset.univ : Finset F)
      (fun g : F => 2 ^ Module.finrank (ZMod 2) (LinearMap.range (g : V →ₗ[ZMod 2] V)))
      (Finset.mem_univ (0 : F))
    rw [← hsplit]
    have h0 : 2 ^ Module.finrank (ZMod 2) (LinearMap.range ((0 : F) : V →ₗ[ZMod 2] V)) = 1 := by
      have hz : ((0 : F) : V →ₗ[ZMod 2] V) = 0 := rfl
      rw [hz, LinearMap.range_zero]
      simp
    rw [h0]
    apply Odd.add_even odd_one
    apply Finset.even_sum
    intro g hg
    rw [Finset.mem_erase] at hg
    have hg0 : g ≠ 0 := hg.1
    have hgp : 1 ≤ Module.finrank (ZMod 2) (LinearMap.range (g : V →ₗ[ZMod 2] V)) := by
      rw [Nat.one_le_iff_ne_zero]
      intro hz
      haveI : Finite ↥(LinearMap.range (g : V →ₗ[ZMod 2] V)) := inferInstance
      haveI : Module.Finite (ZMod 2) ↥(LinearMap.range (g : V →ₗ[ZMod 2] V)) :=
        Module.Finite.of_finite
      have hbot : LinearMap.range (g : V →ₗ[ZMod 2] V) = ⊥ := (Submodule.finrank_eq_zero).mp hz
      exact hg0 (Subtype.ext (LinearMap.range_eq_bot.mp hbot))
    exact ⟨2 ^ (Module.finrank (ZMod 2) (LinearMap.range (g : V →ₗ[ZMod 2] V)) - 1), by
      rw [← two_mul, ← pow_succ', Nat.sub_add_cancel hgp]⟩
  -- ## Splitting off `w = 0`.
  by_cases hFbot : F = ⊥
  · intro i
    refine Or.inl ?_
    have hmem : σ i ∈ F := ⟨i, rfl⟩
    rw [hFbot] at hmem
    exact mem_bot_zmod.mp hmem
  · have hmpos : 1 ≤ Module.finrank (ZMod 2) F := by
      rw [Nat.one_le_iff_ne_zero]
      intro hz
      haveI : Module.Finite (ZMod 2) ↥F := Module.Finite.of_finite
      exact hFbot ((Submodule.finrank_eq_zero).mp hz)
    have hff0 : ff 0 = 2 ^ Module.finrank (ZMod 2) F := by
      rw [hffval 0]
      have hone : (Finset.univ.filter (fun g : F => psiF F 0 g = 0)) = Finset.univ :=
        Finset.filter_true_of_mem (fun g _ => by simp)
      rw [hone, Finset.card_univ, hcardF]
    -- There is a nonzero `w₀` whose fibre is odd.
    have hextract : ∃ w : V, w ≠ 0 ∧ Odd (ff w) := by
      have hs := Finset.add_sum_erase (Finset.univ : Finset V) ff (Finset.mem_univ (0 : V))
      rw [← hTfib, hff0] at hs
      have hSodd : Odd (∑ w ∈ Finset.univ.erase (0 : V), ff w) := by
        have hOdd' : Odd (2 ^ Module.finrank (ZMod 2) F
            + ∑ w ∈ Finset.univ.erase (0 : V), ff w) := by
          rw [hs]; exact hTodd
        have heven : Even (2 ^ Module.finrank (ZMod 2) F) := by
          rw [Nat.even_pow]; exact ⟨even_two, by omega⟩
        by_contra hcon
        rw [Nat.not_odd_iff_even] at hcon
        exact (Nat.not_odd_iff_even.mpr (heven.add hcon)) hOdd'
      obtain ⟨w, hwmem, hwodd⟩ := exists_odd_of_odd_sum hSodd
      exact ⟨w, (Finset.mem_erase.mp hwmem).1, hwodd⟩
    obtain ⟨w₀, hw₀ne, hw₀odd⟩ := hextract
    -- The fibre over `w₀` is nonempty.
    obtain ⟨g₀, hg₀val⟩ : ∃ g₀ : F, psiF F w₀ g₀ = w₀ := by
      rw [hffval w₀] at hw₀odd
      obtain ⟨g₀, hg₀⟩ := Finset.card_pos.mp hw₀odd.pos
      exact ⟨g₀, (Finset.mem_filter.mp hg₀).2⟩
    -- `ff w₀` equals the cardinality of the kernel, which is therefore odd.
    have hcardker : Nat.card ↥(LinearMap.ker (psiF F w₀)) = ff w₀ := by
      rw [hffval w₀, filter_card_eq (fun g : F => psiF F w₀ g = w₀)]
      exact (card_fiber_eq_card_ker (psiF F w₀) hg₀val).symm
    have hoddker : Odd (Nat.card ↥(LinearMap.ker (psiF F w₀))) := by
      rw [hcardker]; exact hw₀odd
    -- Hence the kernel is trivial.
    have hker0 : LinearMap.ker (psiF F w₀) = ⊥ := by
      haveI : Finite ↥(LinearMap.ker (psiF F w₀)) := inferInstance
      haveI : Module.Finite (ZMod 2) ↥(LinearMap.ker (psiF F w₀)) := Module.Finite.of_finite
      have hcard : Nat.card ↥(LinearMap.ker (psiF F w₀))
          = 2 ^ Module.finrank (ZMod 2) ↥(LinearMap.ker (psiF F w₀)) := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := ↥(LinearMap.ker (psiF F w₀))),
          Nat.card_zmod]
      have hfr0 : Module.finrank (ZMod 2) ↥(LinearMap.ker (psiF F w₀)) = 0 := by
        by_contra hne
        have heven : Even (2 ^ Module.finrank (ZMod 2) ↥(LinearMap.ker (psiF F w₀))) := by
          rw [Nat.even_pow]; exact ⟨even_two, hne⟩
        rw [← hcard] at heven
        exact Nat.not_odd_iff_even.mpr heven hoddker
      exact (Submodule.finrank_eq_zero).mp hfr0
    -- Transporting along the `ξ`-orbit of `w₀`: all kernels are trivial.
    have hker_all : ∀ w : V, w ≠ 0 → LinearMap.ker (psiF F w) = ⊥ := by
      intro w hw
      obtain ⟨k, hk⟩ := htrans w₀ w hw₀ne hw
      have hgen : ∀ n : ℕ, LinearMap.ker (psiF F ((ξ ^ n) w₀)) = ⊥ := by
        intro n
        induction n with
        | zero => simpa using hker0
        | succ n ih =>
            show LinearMap.ker (psiF F ((ξ ^ (n + 1)) w₀)) = ⊥
            rw [pow_succ', LinearEquiv.mul_apply]
            exact hker_step ((ξ ^ n) w₀) ih
      rw [← hk]
      exact hgen k
    -- ## Consequently every nonzero element of `F` is the identity.
    intro i
    have hmem : σ i ∈ F := ⟨i, rfl⟩
    by_cases hzero_i : σ i = 0
    · exact Or.inl hzero_i
    · right
      have hgidem : IsIdempotentElem (σ i) := hFidem (σ i) hmem
      have hkerg : LinearMap.ker (σ i) = ⊥ := by
        rw [Submodule.eq_bot_iff]
        intro v hv
        by_contra hv0
        have hmem' : (⟨σ i, hmem⟩ : F) ∈ LinearMap.ker (psiF F v) := by
          rw [LinearMap.mem_ker]; exact hv
        rw [hker_all v hv0] at hmem'
        have hz : (⟨σ i, hmem⟩ : F) = 0 := mem_bot_zmod.mp hmem'
        exact hzero_i (by simpa using congr_arg Subtype.val hz)
      have hfinal : σ i = LinearMap.id := by
        ext v
        have hmem'' : σ i v - v ∈ LinearMap.ker (σ i) := by
          rw [LinearMap.mem_ker]
          have h2 : σ i (σ i v) = σ i v := by
            have hcomp := hgidem
            rw [isIdempotentElem_iff, Module.End.mul_eq_comp] at hcomp
            have := LinearMap.congr_fun hcomp v
            simpa using this
          rw [map_sub, h2, sub_self]
        rw [hkerg] at hmem''
        exact sub_eq_zero.mp (mem_bot_zmod.mp hmem'')
      exact hfinal

/-! ## The multiplicative form -/

/-- Multiplicative form of the Boolean idempotent family lemma.

`W` is a finite group of exponent two (equivalently, a finite `𝔽₂`-vector space written
multiplicatively), `ξ` an automorphism permuting the non-identity elements transitively.
If `σ i` is a family of idempotent endomorphisms, additively closed (`hprod`), and permuted by
`ξ`-conjugation (`hinv`), then every `σ i` is the constant-`1` map or the identity.

We reduce to the additive version `boolean_idempotent_family_univ` by transporting along the
equivalence of monoids `W ≃ Additive W`. -/
theorem boolean_idempotent_family_mul {W : Type*} [Group W] [Finite W]
    (hexp : ∀ g : W, g * g = 1)
    (ξ : W ≃* W)
    (htrans : ∀ a b : W, a ≠ 1 → b ≠ 1 → ∃ k : ℕ, (ξ ^ k) a = b)
    {ι : Type*} [Fintype ι] (σ : ι → W →* W)
    (hidem : ∀ i g, σ i (σ i g) = σ i g)
    (hprod : ∀ i j, ∃ k, ∀ g, σ k g = σ i g * σ j g)
    (hinv : ∃ τ : ι ≃ ι, ∀ i v, σ (τ i) (ξ v) = ξ (σ i v)) :
    ∀ i, (∀ g : W, σ i g = 1) ∨ (∀ g : W, σ i g = g) := by
  -- `W` is commutative, since every element is an involution.
  have hcommW : ∀ a b : W, a * b = b * a := by
    intro a b
    have ha : a⁻¹ = a := inv_eq_of_mul_eq_one_left (hexp a)
    have hb : b⁻¹ = b := inv_eq_of_mul_eq_one_left (hexp b)
    have hab : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_left (hexp (a * b))
    calc a * b = (a * b)⁻¹ := hab.symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [ha, hb]
  letI : CommGroup W := { (inferInstance : Group W) with mul_comm := hcommW }
  -- Make `Additive W` into a `ZMod 2`-vector space.
  have h2' : ∀ v : Additive W, (2 : ℕ) • v = 0 := by
    intro v
    rw [← ofMul_toMul v, ← ofMul_pow, ofMul_eq_zero, pow_two]
    exact hexp (Additive.toMul v)
  haveI hmod : Module (ZMod 2) (Additive W) := AddCommGroup.zmodModule h2'
  -- Transport the family `σ` to linear maps on `Additive W`.
  let σ' : ι → Additive W →ₗ[ZMod 2] Additive W := fun i =>
    AddMonoidHom.toZModLinearMap 2
      { toFun := fun x => Additive.ofMul (σ i (Additive.toMul x))
        map_zero' := by
          show Additive.ofMul (σ i 1) = 0
          rw [map_one]; rfl
        map_add' := fun x y => by
          show Additive.ofMul (σ i (Additive.toMul (x + y))) =
            Additive.ofMul (σ i (Additive.toMul x)) + Additive.ofMul (σ i (Additive.toMul y))
          rw [show Additive.toMul (x + y) = Additive.toMul x * Additive.toMul y from rfl,
            map_mul]
          rfl }
  have hσidem : ∀ i, (σ' i).comp (σ' i) = σ' i := by
    intro i; ext x
    show Additive.ofMul (σ i (σ i (Additive.toMul x))) = Additive.ofMul (σ i (Additive.toMul x))
    rw [hidem]
  have hσadd : ∀ i j, ∃ k, σ' k = σ' i + σ' j := by
    intro i j
    obtain ⟨k, hk⟩ := hprod i j
    refine ⟨k, ?_⟩
    ext x
    show Additive.ofMul (σ k (Additive.toMul x)) =
      Additive.ofMul (σ i (Additive.toMul x)) + Additive.ofMul (σ j (Additive.toMul x))
    rw [← ofMul_mul, hk (Additive.toMul x)]
  -- Transport `ξ`.
  let ξl : Additive W ≃ₗ[ZMod 2] Additive W :=
    LinearEquiv.ofBijective
      (AddMonoidHom.toZModLinearMap 2 (MulEquiv.toAdditive ξ).toAddMonoidHom)
      (MulEquiv.toAdditive ξ).bijective
  have hξapply : ∀ x : Additive W, ξl x = Additive.ofMul (ξ (Additive.toMul x)) := fun _ => rfl
  have hξtrans : ∀ a b : Additive W, a ≠ 0 → b ≠ 0 → ∃ k : ℕ, (ξl ^ k) a = b := by
    intro a b ha hb
    have ha' : Additive.toMul a ≠ 1 := fun hc => ha (by rw [← ofMul_toMul a, hc]; rfl)
    have hb' : Additive.toMul b ≠ 1 := fun hc => hb (by rw [← ofMul_toMul b, hc]; rfl)
    obtain ⟨k, hk⟩ := htrans (Additive.toMul a) (Additive.toMul b) ha' hb'
    refine ⟨k, ?_⟩
    have h1 : ∀ n : ℕ, (ξl ^ n) a = Additive.ofMul ((ξ ^ n) (Additive.toMul a)) := by
      intro n
      induction n with
      | zero => rw [pow_zero, pow_zero]; rfl
      | succ n ih =>
        rw [pow_succ', pow_succ']
        show ξl ((ξl ^ n) a) = Additive.ofMul (ξ ((ξ ^ n) (Additive.toMul a)))
        rw [ih, hξapply, toMul_ofMul]
    rw [h1 k, hk, ofMul_toMul]
  have hσinv : ∃ τ : ι ≃ ι, ∀ i v, σ' (τ i) (ξl v) = ξl (σ' i v) := by
    obtain ⟨τ, hτ⟩ := hinv
    refine ⟨τ, ?_⟩
    intro i v
    show Additive.ofMul (σ (τ i) (Additive.toMul (ξl v))) =
      Additive.ofMul (ξ (σ i (Additive.toMul v)))
    rw [hξapply, toMul_ofMul, hτ i (Additive.toMul v)]
  have hmain := boolean_idempotent_family_univ ξl hξtrans σ' hσidem hσadd hσinv
  intro i
  rcases hmain i with h | h
  · left
    intro g
    have hx := congrArg (fun f : Additive W →ₗ[ZMod 2] Additive W => f (Additive.ofMul g)) h
    simp only [LinearMap.zero_apply] at hx
    exact ofMul_eq_zero.mp hx
  · right
    intro g
    have hx := congrArg (fun f : Additive W →ₗ[ZMod 2] Additive W => f (Additive.ofMul g)) h
    simp only [LinearMap.id_apply] at hx
    exact Additive.ofMul.injective hx

end Work.Higman
