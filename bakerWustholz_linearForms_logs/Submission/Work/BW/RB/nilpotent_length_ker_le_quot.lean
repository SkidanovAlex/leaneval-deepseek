import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `ℓ(ker f) ≤ ℓ(coker f)` for a nilpotent endomorphism

For an endomorphism `f` of a module `M` over a (possibly noncommutative) ring `S` with `f ^ n = 0`,
the length of the kernel of `f` is at most the length of its cokernel `M ⧸ range f`.

The proof has two halves.

* If `ℓ(M ⧸ range f) = ⊤` there is nothing to prove.
* Otherwise the two short exact sequences
  `0 → ker f → M → range f → 0` and `0 → range f → M → M ⧸ range f → 0`
  give `ℓ(ker f) + ℓ(range f) = ℓ(M) = ℓ(range f) + ℓ(M ⧸ range f)`, and canceling `ℓ(range f)`
  yields the claim.  Cancellation is legal because `ℓ(range f) ≠ ⊤`: indeed, for the descending
  filtration `M = B₀ ⊇ B₁ ⊇ ⋯ ⊇ Bₙ = 0` with `Bᵢ = range (f ^ i)`, each `Bᵢ ⧸ Bᵢ₊₁` is a quotient
  of `range f / range f²`, which is a quotient of `M ⧸ range f` via `f`; hence all `Bᵢ` are of
  finite length by additivity.
-/

namespace Work.BW.RB

/-- Length is additive for a submodule and its quotient. -/
private lemma rb_len_quot {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (N : Submodule R M) :
    Module.length R M = Module.length R N + Module.length R (M ⧸ N) :=
  Module.length_eq_add_of_exact (Submodule.subtype N) (Submodule.mkQ N)
    (Submodule.subtype_injective N) (Submodule.mkQ_surjective N)
    (LinearMap.exact_subtype_mkQ N)

/-- Length is additive for a pair of nested submodules `N ≤ P`: the quotient `P ⧸ N` is realized
as the image of `P` in `M ⧸ N`. -/
private lemma rb_len_nested {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {N P : Submodule R M} (h : N ≤ P) :
    Module.length R P = Module.length R N + Module.length R (Submodule.map (Submodule.mkQ N) P) := by
  set g : P →ₗ[R] M ⧸ N := (Submodule.mkQ N).comp P.subtype with hg
  have hker : LinearMap.ker g = N.comap P.subtype := by
    ext x
    simp [hg, LinearMap.mem_ker, Submodule.mem_comap]
  have hrange : LinearMap.range g = Submodule.map (Submodule.mkQ N) P := by
    rw [hg, LinearMap.range_comp, Submodule.range_subtype]
  have hstd := rb_len_quot (R := R) (M := P) (LinearMap.ker g)
  rw [hker] at hstd
  have h1 : Module.length R (N.comap P.subtype) = Module.length R N :=
    (Submodule.comapSubtypeEquivOfLe h).length_eq
  have h2 : Module.length R (P ⧸ N.comap P.subtype) =
      Module.length R (Submodule.map (Submodule.mkQ N) P) := by
    have hh := (LinearMap.quotKerEquivRange g).length_eq
    rw [hker] at hh
    rw [hrange] at hh
    exact hh
  rw [h1, h2] at hstd
  exact hstd

/-- The image of `range f` under `f ^ i` is `range (f ^ (i+1))`. -/
private lemma rb_map_range_pow {S M : Type*} [Ring S] [AddCommGroup M] [Module S M]
    (f : M →ₗ[S] M) (i : ℕ) :
    Submodule.map (f^i) (LinearMap.range f) = LinearMap.range (f^(i+1)) := by
  rw [← LinearMap.range_comp f (f^i), pow_succ]
  rfl

/-- The ranges of the powers of an endomorphism form a descending chain. -/
private lemma rb_range_pow_succ_le {S M : Type*} [Ring S] [AddCommGroup M] [Module S M]
    (f : M →ₗ[S] M) (i : ℕ) :
    LinearMap.range (f^(i+1)) ≤ LinearMap.range (f^i) := by
  rw [pow_succ]
  exact LinearMap.range_comp_le_range f (f^i)

theorem nilpotent_length_ker_le_quot {S M : Type*} [Ring S] [AddCommGroup M] [Module S M]
    (f : M →ₗ[S] M) (n : ℕ) (h : f ^ n = 0) :
    Module.length S (LinearMap.ker f) ≤ Module.length S (M ⧸ LinearMap.range f) := by
  by_cases hc : Module.length S (M ⧸ LinearMap.range f) = ⊤
  · rw [hc]; exact le_top
  set B : ℕ → Submodule S M := fun i => LinearMap.range (f ^ i) with hB
  have hB0 : B 0 = ⊤ := by simp [hB, pow_zero, Module.End.one_eq_id]
  have hB1 : B 1 = LinearMap.range f := by simp [hB]
  have hBn : B n = ⊥ := by simp [hB, h]
  have hmap : ∀ i, Submodule.map (f^i) (LinearMap.range f) = B (i+1) := by
    intro i
    rw [rb_map_range_pow, hB]
  -- `Bᵢ ⧸ Bᵢ₊₁` is a quotient of `M ⧸ range f`, hence of length at most `ℓ(M ⧸ range f)`
  have hQle : ∀ i, Module.length S (Submodule.map (Submodule.mkQ (B (i+1))) (B i)) ≤
      Module.length S (M ⧸ B 1) := by
    intro i
    have hle : B 1 ≤ (B (i+1)).comap (f^i) := by
      rw [hB1, ← Submodule.map_le_iff_le_comap, hmap i]
    have hrange : LinearMap.range ((B 1).mapQ (B (i+1)) (f^i) hle) =
        Submodule.map (Submodule.mkQ (B (i+1))) (B i) :=
      Submodule.range_mapQ (B 1) (B (i+1)) (f^i) hle
    have h2 := Module.length_le_of_surjective ((B 1).mapQ (B (i+1)) (f^i) hle).rangeRestrict
      (LinearMap.surjective_rangeRestrict _)
    rwa [hrange] at h2
  -- additivity along the filtration
  have hstep : ∀ i, Module.length S (B i) =
      Module.length S (B (i+1)) +
        Module.length S (Submodule.map (Submodule.mkQ (B (i+1))) (B i)) := by
    intro i
    have hmono : B (i+1) ≤ B i := by
      rw [hB]
      exact rb_range_pow_succ_le f i
    exact rb_len_nested hmono
  -- hence all `Bᵢ` have finite length
  have hfin : ∀ k, k ≤ n → Module.length S (B (n - k)) ≠ ⊤ := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [Nat.sub_zero, hBn, Module.length_bot]
      simp
    | succ k ih =>
      intro hk
      have hk' : k ≤ n := Nat.le_of_succ_le hk
      have hb : Module.length S (B (n - k)) ≠ ⊤ := ih hk'
      have hsub : n - (k + 1) + 1 = n - k := by omega
      have hq : Module.length S (Submodule.map (Submodule.mkQ (B (n - k)))
          (B (n - (k + 1)))) ≠ ⊤ := by
        have := hQle (n - (k + 1))
        rw [hsub] at this
        exact fun htop => hc (top_le_iff.mp (htop ▸ this))
      have hst := hstep (n - (k + 1))
      rw [hsub] at hst
      rw [hst]
      intro hcontra
      rcases ENat.add_eq_top.mp hcontra with hh | hh
      · exact hb hh
      · exact hq hh
  have hM : Module.length S M ≠ ⊤ := by
    have := hfin n le_rfl
    rwa [Nat.sub_self, hB0, Module.length_top] at this
  -- the two exact sequences
  have h1 : Module.length S M =
      Module.length S (LinearMap.ker f) + Module.length S (LinearMap.range f) :=
    Module.length_eq_add_of_exact (LinearMap.ker f).subtype f.rangeRestrict
      (Submodule.subtype_injective _) (LinearMap.surjective_rangeRestrict f)
      (by rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype])
  have h2 : Module.length S M = Module.length S (LinearMap.range f) +
      Module.length S (M ⧸ LinearMap.range f) :=
    Module.length_eq_add_of_exact (Submodule.subtype _) (Submodule.mkQ _)
      (Submodule.subtype_injective _) (Submodule.mkQ_surjective _)
      (LinearMap.exact_subtype_mkQ _)
  have hne : Module.length S (LinearMap.range f) ≠ ⊤ := by
    intro htop
    exact hM (by rw [h2, htop, top_add])
  -- cancel `ℓ(range f)`
  have key := h1.symm.trans h2
  rw [add_comm (Module.length S (LinearMap.ker f)) (Module.length S (LinearMap.range f))] at key
  exact (WithTop.add_left_cancel hne key).le

end Work.BW.RB
