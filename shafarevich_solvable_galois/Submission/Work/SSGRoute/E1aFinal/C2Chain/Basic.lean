import Mathlib
import Submission.Work.SSGRoute.E1aFinal.C2Chain.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `C₂`-lattice chain (S3): lattice-theoretic core

This file contains the two lattice-theoretic inputs of
`Work.SSGRoute.E1aFinal.hasseExt1_C2_lattice_chain`:

* `finite_quotient_of_two_smul_mem`: for a finite free `ℤ`-lattice `V` and a `Coeff`-submodule
  `D ⊇ 2V`, the quotient `V ⧸ D` is finite;
* `exists_chain_twoStep`: such a quotient can be refined into a chain of index-two extensions.

Since `Coeff = ULift ℤ`, Mathlib's `ULift`-scalar instances compete with the `Module Coeff V`
structure; we remove them below so that `c • x` always denotes the *module* action.
-/

attribute [-instance] ULift.smulLeft
attribute [-instance] ULift.smulZeroClass
attribute [-instance] ULift.distribSMul
attribute [-instance] ULift.distribMulAction
attribute [-instance] ULift.mulAction
attribute [-instance] ULift.smulWithZero
attribute [-instance] ULift.mulActionWithZero

namespace Work.SSGRoute.E1aFinal

open scoped BigOperators
open Module

noncomputable section

/-- The canonical identification `ℤ → ULift ℤ` in `Coeff`. -/
lemma coeff_intCast_eq (n : ℤ) : ((n : ℤ) : SSGRoute.PTExt.Coeff) = ULift.up n :=
  ULift.ext (map_intCast (ULift.ringEquiv : ULift.{0} ℤ ≃+* ℤ) n)

/-- The `Coeff`-action agrees with the canonical `ℤ`-action. -/
lemma coeff_smul_eq_int_smul {V : Type*} [AddCommGroup V] [Module SSGRoute.PTExt.Coeff V]
    (c : SSGRoute.PTExt.Coeff) (x : V) : c • x = c.down • x :=
  (congrArg (fun r : SSGRoute.PTExt.Coeff => r • x) (show c = ((c.down : ℤ) : SSGRoute.PTExt.Coeff)
    from (coeff_intCast_eq c.down).symm)).trans (Int.cast_smul_eq_zsmul _ c.down x)

/-- `2 • x = 2 • x` for the `Coeff`- and `ℤ`-actions. -/
lemma coeff_two_smul {V : Type*} [AddCommGroup V] [Module SSGRoute.PTExt.Coeff V] (x : V) :
    (2 : SSGRoute.PTExt.Coeff) • x = (2 : ℤ) • x := by
  rw [show (2 : SSGRoute.PTExt.Coeff) = ((2 : ℤ) : SSGRoute.PTExt.Coeff)
    from (coeff_intCast_eq 2).symm]
  exact Int.cast_smul_eq_zsmul _ _ _

/-- A `Coeff`-multiple of `m` lies in the span of `m`. -/
lemma smul_mem_span_singleton {V : Type*} [AddCommGroup V] [Module SSGRoute.PTExt.Coeff V]
    (c : SSGRoute.PTExt.Coeff) (m : V) :
    c • m ∈ Submodule.span SSGRoute.PTExt.Coeff ({m} : Set V) :=
  Submodule.mem_span_singleton.mpr ⟨c, rfl⟩

/-- Every integer is even or odd. -/
lemma int_even_or_odd_form (n : ℤ) :
    (∃ t : ℤ, n = 2 * t) ∨ (∃ t : ℤ, n = 2 * t + 1) := by
  rcases Int.even_or_odd n with ⟨k, hk⟩ | hk
  · exact Or.inl ⟨k, by rw [hk, two_mul]⟩
  · exact Or.inr hk

/-- The `ℤ`-scalar action preserves `Coeff`-submodules. -/
lemma zsmul_mem {V : Type*} [AddCommGroup V] [Module SSGRoute.PTExt.Coeff V]
    (L : Submodule SSGRoute.PTExt.Coeff V) (n : ℤ) {x : V} (hx : x ∈ L) : n • x ∈ L := by
  rw [← Int.cast_smul_eq_zsmul SSGRoute.PTExt.Coeff n x]
  exact L.smul_mem _ hx

lemma exists_not_mem_of_ne_top {V : Type*} [AddCommGroup V] [Module SSGRoute.PTExt.Coeff V]
    {L : Submodule SSGRoute.PTExt.Coeff V} (h : L ≠ ⊤) : ∃ m : V, m ∉ L := by
  by_contra hc
  push Not at hc
  exact h (Submodule.eq_top_iff'.mpr hc)

lemma exists_not_mem_or_top {V : Type*} [AddCommGroup V] [Module SSGRoute.PTExt.Coeff V]
    (L : Submodule SSGRoute.PTExt.Coeff V) : ∃ m : V, ∀ _ : L ≠ ⊤, m ∉ L := by
  by_cases h : L = ⊤
  · exact ⟨0, fun hh => absurd h hh⟩
  · obtain ⟨m, hm⟩ := exists_not_mem_of_ne_top h
    exact ⟨m, fun _ => hm⟩

/-- A chosen element of `V` outside `L` (arbitrary when `L = ⊤`). -/
def extChoice {V : Type*} [AddCommGroup V] [Module SSGRoute.PTExt.Coeff V]
    (L : Submodule SSGRoute.PTExt.Coeff V) : V :=
  Classical.choose (exists_not_mem_or_top L)

lemma extChoice_not_mem {V : Type*} [AddCommGroup V] [Module SSGRoute.PTExt.Coeff V]
    {L : Submodule SSGRoute.PTExt.Coeff V} (h : L ≠ ⊤) : extChoice L ∉ L :=
  Classical.choose_spec (exists_not_mem_or_top L) h

/-- One step of the greedy refinement: adjoin a chosen element. -/
def extStep {V : Type*} [AddCommGroup V] [Module SSGRoute.PTExt.Coeff V]
    (L : Submodule SSGRoute.PTExt.Coeff V) : Submodule SSGRoute.PTExt.Coeff V :=
  L ⊔ (SSGRoute.PTExt.Coeff ∙ extChoice L)

lemma extStep_eq {V : Type*} [AddCommGroup V] [Module SSGRoute.PTExt.Coeff V]
    (L : Submodule SSGRoute.PTExt.Coeff V) :
    extStep L = L ⊔ (SSGRoute.PTExt.Coeff ∙ extChoice L) := rfl

lemma le_extStep {V : Type*} [AddCommGroup V] [Module SSGRoute.PTExt.Coeff V]
    (L : Submodule SSGRoute.PTExt.Coeff V) : L ≤ extStep L := le_sup_left

lemma extChoice_mem_extStep {V : Type*} [AddCommGroup V] [Module SSGRoute.PTExt.Coeff V]
    (L : Submodule SSGRoute.PTExt.Coeff V) : extChoice L ∈ extStep L :=
  Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)

theorem finite_quotient_of_two_smul_mem {V : Type*} [AddCommGroup V]
    [Module SSGRoute.PTExt.Coeff V] [Module.Finite ℤ V] [Module.Free ℤ V]
    (D : Submodule SSGRoute.PTExt.Coeff V)
    (h2 : ∀ x : V, x + x ∈ D) : Finite (V ⧸ D) := by
  classical
  obtain ⟨r, b⟩ : Σ n, Basis (Fin n) ℤ V := ⟨_, Module.finBasis ℤ V⟩
  refine Finite.of_surjective
    (fun t : Fin r → ZMod 2 =>
      Submodule.Quotient.mk (p := D) (∑ i, (((t i).val : ℤ)) • b i)) ?_
  intro y
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective D y
  refine ⟨fun i => (b.repr x i : ZMod 2), ?_⟩
  have hdiv : ∀ i, (2 : ℤ) ∣ b.repr x i - (((b.repr x i : ZMod 2)).val : ℤ) := by
    intro i
    have h1 : ((((b.repr x i : ZMod 2)).val : ℤ) : ZMod 2) =
        ((b.repr x i : ℤ) : ZMod 2) := by
      rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    have h2' : b.repr x i ≡ ((((b.repr x i : ZMod 2)).val : ℤ)) [ZMOD (2 : ℤ)] :=
      (ZMod.intCast_eq_intCast_iff (b.repr x i)
        ((((b.repr x i : ZMod 2)).val : ℤ)) 2).mp h1.symm
    rw [Int.modEq_iff_dvd] at h2'
    obtain ⟨c, hc⟩ := h2'
    exact ⟨-c, by omega⟩
  have key : x - ∑ i, (((b.repr x i : ZMod 2)).val : ℤ) • b i ∈ D := by
    have hsum : x - ∑ i, (((b.repr x i : ZMod 2)).val : ℤ) • b i =
        ∑ i, (b.repr x i - (((b.repr x i : ZMod 2)).val : ℤ)) • b i := by
      have h1 : x - ∑ i, (((b.repr x i : ZMod 2)).val : ℤ) • b i =
          (∑ i, (b.repr x i) • b i) - ∑ i, (((b.repr x i : ZMod 2)).val : ℤ) • b i :=
        congrArg (fun w : V => w - ∑ i, (((b.repr x i : ZMod 2)).val : ℤ) • b i)
          (b.sum_repr x).symm
      rw [h1, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => (sub_smul _ _ _).symm
    rw [hsum]
    choose k hk using hdiv
    have hrewrite : (∑ i, (b.repr x i - (((b.repr x i : ZMod 2)).val : ℤ)) • b i) =
        (2 : ℤ) • (∑ i, k i • b i) := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [hk i, mul_smul]
    rw [hrewrite, two_smul]
    exact h2 _
  rw [Submodule.Quotient.eq]
  simpa only [neg_sub] using neg_mem key

theorem exists_chain_twoStep {V : Type*} [AddCommGroup V]
    [Module SSGRoute.PTExt.Coeff V]
    (D : Submodule SSGRoute.PTExt.Coeff V) (τ : V →ₗ[SSGRoute.PTExt.Coeff] V)
    (hτ : ∀ x : V, τ x - x ∈ D) (h2 : ∀ x : V, x + x ∈ D)
    (hfin : Finite (V ⧸ D)) :
    ∃ (n : ℕ) (c : Fin (n + 1) → Submodule SSGRoute.PTExt.Coeff V),
      c 0 = D ∧ c (Fin.last n) = ⊤ ∧
      (∀ i : Fin (n + 1), ∀ x ∈ c i, τ x ∈ c i) ∧
      (∀ i : Fin n, TwoStep (c i.castSucc) (c i.succ)) := by
  classical
  -- the greedy refinement
  let L : ℕ → Submodule SSGRoute.PTExt.Coeff V := Nat.rec D (fun _ Lk => extStep Lk)
  have hLs : ∀ k, L (k + 1) = extStep (L k) := fun k => rfl
  have hDL : ∀ k, D ≤ L k := by
    intro k
    induction k with
    | zero => exact le_rfl
    | succ k ih => rw [hLs]; exact le_trans ih (le_extStep _)
  have hstab : ∀ k, ∀ x ∈ L k, τ x ∈ L k := by
    intro k
    induction k with
    | zero =>
        intro x hx
        have hx' : x ∈ D := hx
        have hxτ : τ x = x + (τ x - x) := by abel
        rw [hxτ]
        exact D.add_mem hx' (hτ x)
    | succ k ih =>
        rw [hLs]
        intro x hx
        rw [extStep_eq] at hx ⊢
        obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hx
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hz
        set m : V := extChoice (L k) with hm
        have hmL : τ m - m ∈ L k := hDL k (hτ m)
        have hx' : τ x = τ y + c • m + c • (τ m - m) := by
          have hxz : x = y + c • m := by rw [← hyz, ← hc]
          calc τ x = τ (y + c • m) := by rw [hxz]
            _ = τ y + c • τ m := by rw [map_add, map_smul]
            _ = τ y + c • (m + (τ m - m)) := by
                  rw [show m + (τ m - m) = τ m by abel]
            _ = τ y + (c • m + c • (τ m - m)) := by rw [smul_add]
            _ = τ y + c • m + c • (τ m - m) := by rw [add_assoc]
        rw [hx']
        refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
        · exact Submodule.mem_sup_left (ih y hy)
        · exact Submodule.mem_sup_right (smul_mem_span_singleton c m)
        · exact Submodule.mem_sup_left (Submodule.smul_mem (L k) c hmL)
  have hfinQ : ∀ (L' : Submodule SSGRoute.PTExt.Coeff V), D ≤ L' → Finite (V ⧸ L') := by
    intro L' h
    refine Finite.of_surjective
      (Submodule.mapQ D L' (LinearMap.id : V →ₗ[SSGRoute.PTExt.Coeff] V) h) ?_
    intro z
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective L' z
    exact ⟨Submodule.Quotient.mk x, by simp [Submodule.mapQ_apply]⟩
  have hcard_lt : ∀ (L' : Submodule SSGRoute.PTExt.Coeff V), D ≤ L' → L' ≠ ⊤ →
      Nat.card (V ⧸ extStep L') < Nat.card (V ⧸ L') := by
    intro L' hDL' hL'
    have hle : L' ≤ extStep L' := le_extStep L'
    have hmL' : extChoice L' ∉ L' := extChoice_not_mem hL'
    have hm_step : extChoice L' ∈ extStep L' := extChoice_mem_extStep L'
    haveI : Finite (V ⧸ L') := hfinQ L' hDL'
    haveI : Finite (V ⧸ extStep L') := hfinQ _ (le_trans hDL' hle)
    haveI : Fintype (V ⧸ L') := Fintype.ofFinite _
    haveI : Fintype (V ⧸ extStep L') := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    refine Fintype.card_lt_of_surjective_not_injective
      (Submodule.mapQ L' (extStep L') (LinearMap.id) hle) ?_ ?_
    · intro z
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (extStep L') z
      exact ⟨Submodule.Quotient.mk x, by simp [Submodule.mapQ_apply]⟩
    · intro hinj
      have h1 : Submodule.mapQ L' (extStep L') (LinearMap.id) hle
            (Submodule.Quotient.mk (extChoice L')) =
          Submodule.mapQ L' (extStep L') (LinearMap.id) hle
            (Submodule.Quotient.mk 0) := by
        rw [Submodule.mapQ_apply, Submodule.mapQ_apply]
        simp [hm_step]
      have h2 : Submodule.Quotient.mk (p := L') (extChoice L') ≠
          Submodule.Quotient.mk (p := L') 0 := by
        intro hh
        rw [Submodule.Quotient.eq] at hh
        exact hmL' (by simpa using hh)
      exact h2 (hinj h1)
  have hbound : ∀ k, (∀ i < k, L i ≠ ⊤) → Nat.card (V ⧸ L k) + k ≤ Nat.card (V ⧸ D) := by
    intro k
    induction k with
    | zero => intro _; exact le_rfl
    | succ k ih =>
        intro h
        have hk : L k ≠ ⊤ := h k (Nat.lt_succ_self k)
        have hik : ∀ i < k, L i ≠ ⊤ := fun i hi => h i (Nat.lt_trans hi (Nat.lt_succ_self k))
        have ih' := ih hik
        have hlt := hcard_lt (L k) (hDL k) hk
        rw [hLs]
        omega
  have hex : ∃ k, L k = ⊤ := by
    by_contra h
    have h' : ∀ k, L k ≠ ⊤ := fun k hk => h ⟨k, hk⟩
    have hb := hbound (Nat.card (V ⧸ D) + 1) (fun i _ => h' i)
    omega
  have htwoStep : ∀ (L' : Submodule SSGRoute.PTExt.Coeff V), D ≤ L' → L' ≠ ⊤ →
      TwoStep L' (extStep L') := by
    intro L' hDL' hL'
    refine ⟨le_extStep L', extChoice L', extChoice_mem_extStep L', extChoice_not_mem hL', ?_⟩
    intro x hx
    rw [extStep_eq] at hx
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hx
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hz
    set m : V := extChoice L' with hm
    have hm2 : (2 : ℤ) • m ∈ L' := by
      rw [two_smul]; exact hDL' (h2 m)
    have hxz : x = y + c • m := by rw [← hyz, ← hc]
    rcases int_even_or_odd_form c.down with ⟨t, ht⟩ | ⟨t, ht⟩
    · left
      have hx' : x = y + t • ((2 : ℤ) • m) := by
        rw [hxz, coeff_smul_eq_int_smul, ht, mul_comm (2 : ℤ) t, mul_smul]
      rw [hx']
      exact L'.add_mem hy (zsmul_mem L' t hm2)
    · right
      have hx' : x - m = y + t • ((2 : ℤ) • m) := by
        rw [hxz, coeff_smul_eq_int_smul, ht, add_smul, one_smul, mul_comm (2 : ℤ) t, mul_smul]
        abel
      rw [hx']
      exact L'.add_mem hy (zsmul_mem L' t hm2)
  let n : ℕ := @Nat.find (fun k => L k = ⊤) (fun k => Classical.propDecidable _) hex
  have hn : L n = ⊤ :=
    @Nat.find_spec (fun k => L k = ⊤) (fun k => Classical.propDecidable _) hex
  have hmin : ∀ m, m < n → L m ≠ ⊤ := fun m hm =>
    @Nat.find_min (fun k => L k = ⊤) (fun k => Classical.propDecidable _) hex m hm
  refine ⟨n, fun i => L i, rfl, hn, ?_, ?_⟩
  · intro i x hx
    exact hstab i x hx
  · intro i
    have hi : (i : ℕ) < n := i.isLt
    have hne : L (i : ℕ) ≠ ⊤ := hmin _ hi
    have hts := htwoStep (L (i : ℕ)) (hDL _) hne
    simpa [hLs] using hts

end

end Work.SSGRoute.E1aFinal
