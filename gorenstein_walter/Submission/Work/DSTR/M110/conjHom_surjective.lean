/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Spatiality of `Aut(PSL(2,q))` (A6): every automorphism of `PSL(2,q)` is conjugation by an
element of `PΓL(2,q)`

For `q = p^k`, `p` odd, `q ≥ 5`, the map
`conjHom : PΓL(2,q) →* Aut(PSL(2,q))`, `π ↦ (g ↦ π g π⁻¹)`, is surjective.

The proof is the classical one, done on the projective line `ℙ¹(q)`:

* the *root subgroups* are the subgroups of `PSL(2,q)` of order `q = p^k`; by
  `Work.DSTR.M110.Aut.eqTranslSub` a root subgroup fixing `∞` is the translation group `U₀`,
  and every root subgroup has a unique fixed point on `ℙ¹(q)` (`Work.DSTR.M110.fp`);
* hence `x ↦ (the root subgroup with fixed point x)` is a bijection
  `ℙ¹(q) ≃ {H ≤ PSL(2,q) | |H| = q}` (`fp` is bijective);
* an automorphism `α` permutes the root subgroups, so transports along this bijection to a
  permutation `φ` of `ℙ¹(q)`; the equivariance `fp (gHg⁻¹) = g · fp H` gives
  `φ (g x) = α(g) (φ x)`, i.e. `φ g φ⁻¹ = α g`;
* so `φ` normalizes `pslImage` and hence lies in `PΓL(2,q)` (step A3,
  `Work.AUTL2.Normalizer.le_pgammaL`), and `conjHom φ = α`.
-/
import Mathlib
import Submission.Work.DSTR.M110.Conj
import Submission.Work.DSTR.M110.Normalizer.le_pgammaL
import Submission.Work.DSTR.M110.Galois.decomposition
import Submission.Work.DSTR.M110.Aut.centralizer
import Submission.Work.DSTR.M110.Roots
import Submission.Work.DSTR.M110.Aut.eqTranslSub

open scoped MatrixGroups LinearAlgebra.Projectivization
open OnePoint

namespace Work.DSTR.M110

variable (p k : ℕ) [Fact p.Prime] [Fintype (GaloisField p k)] [DecidableEq (GaloisField p k)]

/-! ## The root subgroup fixing `∞` is `U₀` -/

/-- The `PSL(2,p^k)`-form of `Work.DSTR.M110.Aut.eqTranslSub`: a subgroup of `PG p k` of order `p^k`
all of whose elements fix `∞` is the translation group `U₀`. -/
theorem eq_U0_of_le_stab_of_card (hp : Odd p) (hq : 5 ≤ p ^ k) (H : Subgroup (PG p k))
    (hH : H ≤ Stab p k (∞ : Pl p k)) (hcard : Nat.card H = p ^ k) : H = U0 p k := by
  have hKle : H.map (Work.AUTL2.pslImage (GaloisField p k)).subtype ≤
      Work.AUTL2.pslImage (GaloisField p k) := by
    rintro g ⟨h, -, rfl⟩
    exact h.2
  have hKcard : Nat.card (H.map (Work.AUTL2.pslImage (GaloisField p k)).subtype) = p ^ k := by
    rw [Subgroup.card_map_of_injective Subtype.coe_injective, hcard]
  have hKfix : ∀ g ∈ H.map (Work.AUTL2.pslImage (GaloisField p k)).subtype,
      g (∞ : Pl p k) = ∞ := by
    rintro g ⟨h, hh, rfl⟩
    exact MulAction.mem_stabilizer_iff.mp (hH hh)
  have hK := Work.DSTR.M110.Aut.eqTranslSub p k hp hq
    (H.map (Work.AUTL2.pslImage (GaloisField p k)).subtype) hKle hKcard hKfix
  refine le_antisymm ?_ ?_
  · intro h hh
    rw [mem_U0_iff]
    have hmem : (h : Equiv.Perm (Pl p k)) ∈
        H.map (Work.AUTL2.pslImage (GaloisField p k)).subtype := ⟨h, hh, rfl⟩
    rwa [hK] at hmem
  · intro u hu
    rw [mem_U0_iff] at hu
    have hmem : (u : Equiv.Perm (Pl p k)) ∈
        H.map (Work.AUTL2.pslImage (GaloisField p k)).subtype := by
      rw [hK]; exact hu
    obtain ⟨h, hh, hhu⟩ := hmem
    have hEq : h = u := Subtype.ext hhu
    rwa [← hEq]

/-! ## The fixed-point map on root subgroups -/

/-- The fixed point of a root subgroup. -/
noncomputable def fp (hk : k ≠ 0) (H : Root p k) : Pl p k :=
  Classical.choose (exists_fixed_point_of_card p k hk H.1 H.2)

lemma fp_fixes (hk : k ≠ 0) (H : Root p k) :
    ∀ h ∈ H.1, h • fp p k hk H = fp p k hk H :=
  Classical.choose_spec (exists_fixed_point_of_card p k hk H.1 H.2)

/-- Membership in a conjugate root subgroup. -/
lemma mem_Root_conj {g : PG p k} {H : Root p k} {u : PG p k} :
    u ∈ (Root.conj p k g H).1 ↔ ∃ t ∈ H.1, g * t * g⁻¹ = u := by
  rw [Root.conj_val, Subgroup.mem_map]
  constructor
  · rintro ⟨t, ht, htu⟩
    exact ⟨t, ht, by rw [← htu]; exact MulAut.conj_apply g t⟩
  · rintro ⟨t, ht, htu⟩
    exact ⟨t, ht, by show (MulAut.conj g) t = u; rw [MulAut.conj_apply, htu]⟩

/-- A conjugate of a root subgroup whose fixed point has been moved to `∞` fixes `∞`. -/
lemma conj_le_stab (hp : Odd p) (hq : 5 ≤ p ^ k) (hk : k ≠ 0) (H : Root p k) (g : PG p k)
    (hg : g • fp p k hk H = ∞) : (Root.conj p k g H).1 ≤ Stab p k (∞ : Pl p k) := by
  intro u hu
  rw [Stab, MulAction.mem_stabilizer_iff]
  obtain ⟨t, ht, htu⟩ := (mem_Root_conj p k).mp hu
  rw [← htu]
  change (g * t * g⁻¹ : PG p k) • (∞ : Pl p k) = ∞
  calc (g * t * g⁻¹ : PG p k) • (∞ : Pl p k)
      = (g * t * g⁻¹ : PG p k) • (g • fp p k hk H) := by rw [hg]
    _ = g • (t • (g⁻¹ • (g • fp p k hk H))) := by rw [mul_smul, mul_smul]
    _ = g • (t • fp p k hk H) := by rw [inv_smul_smul]
    _ = g • fp p k hk H := by rw [fp_fixes p k hk H t ht]
    _ = ∞ := hg

/-- `fp` is the *unique* fixed point. -/
lemma fp_eq_of_fixes (hp : Odd p) (hq : 5 ≤ p ^ k) (hk : k ≠ 0) (H : Root p k) {x : Pl p k}
    (hx : ∀ h ∈ H.1, h • x = x) : fp p k hk H = x := by
  obtain ⟨γ, hγ⟩ := exists_smul_eq p k (fp p k hk H) (∞ : Pl p k)
  have hEq : (Root.conj p k γ H).1 = U0 p k :=
    eq_U0_of_le_stab_of_card p k hp hq _ (conj_le_stab p k hp hq hk H γ hγ)
      (Root.conj p k γ H).2
  have hxU : ∀ u ∈ U0 p k, u • (γ • x) = γ • x := by
    intro u hu
    have hu' : u ∈ (Root.conj p k γ H).1 := by rw [hEq]; exact hu
    obtain ⟨t, ht, htu⟩ := (mem_Root_conj p k).mp hu'
    rw [← htu]
    change (γ * t * γ⁻¹ : PG p k) • (γ • x) = γ • x
    calc (γ * t * γ⁻¹ : PG p k) • (γ • x)
        = γ • (t • (γ⁻¹ • (γ • x))) := by rw [mul_smul, mul_smul]
      _ = γ • (t • x) := by rw [inv_smul_smul]
      _ = γ • x := by rw [hx t ht]
  have h1 : γ • x = ∞ := eq_infty_of_U0_fixes p k (γ • x) hxU
  have h2 : γ • x = γ • fp p k hk H := by rw [h1, hγ]
  have h3 : x = fp p k hk H := by
    have := congrArg (fun z => (γ : PG p k)⁻¹ • z) h2
    simpa only [inv_smul_smul] using this
  exact h3.symm

lemma fp_injective (hp : Odd p) (hq : 5 ≤ p ^ k) (hk : k ≠ 0) :
    Function.Injective (fp p k hk) := by
  intro H H' h
  obtain ⟨γ, hγ⟩ := exists_smul_eq p k (fp p k hk H) (∞ : Pl p k)
  have hγ' : γ • fp p k hk H' = ∞ := by rw [← h]; exact hγ
  have h1 : H.1.map (MulAut.conj γ).toMonoidHom = U0 p k :=
    eq_U0_of_le_stab_of_card p k hp hq _ (conj_le_stab p k hp hq hk H γ hγ)
      (Root.conj p k γ H).2
  have h2 : H'.1.map (MulAut.conj γ).toMonoidHom = U0 p k :=
    eq_U0_of_le_stab_of_card p k hp hq _ (conj_le_stab p k hp hq hk H' γ hγ')
      (Root.conj p k γ H').2
  have hmap : H.1.map (MulAut.conj γ).toMonoidHom = H'.1.map (MulAut.conj γ).toMonoidHom := by
    rw [h1, h2]
  exact Subtype.ext (Subgroup.map_injective (f := (MulAut.conj γ).toMonoidHom)
    (MulAut.conj γ).injective hmap)

lemma fp_surjective (hp : Odd p) (hq : 5 ≤ p ^ k) (hk : k ≠ 0) :
    Function.Surjective (fp p k hk) := by
  intro x
  obtain ⟨γ, hγ⟩ := exists_smul_eq p k (∞ : Pl p k) x
  refine ⟨Root.conj p k γ (⟨U0 p k, card_U0 p k hk⟩ : Root p k), ?_⟩
  refine fp_eq_of_fixes p k hp hq hk _ ?_
  intro u hu
  obtain ⟨t, ht, htu⟩ := (mem_Root_conj p k).mp hu
  rw [← htu]
  change (γ * t * γ⁻¹ : PG p k) • x = x
  calc (γ * t * γ⁻¹ : PG p k) • x
      = γ • (t • (γ⁻¹ • x)) := by rw [mul_smul, mul_smul]
    _ = γ • (t • (∞ : Pl p k)) := by rw [← hγ, inv_smul_smul]
    _ = γ • (∞ : Pl p k) := by
        rw [MulAction.mem_stabilizer_iff.mp (U0_le_stab p k ht)]
    _ = x := hγ

/-- Conjugation of root subgroups is compatible with `fp`. -/
lemma fp_conj (hp : Odd p) (hq : 5 ≤ p ^ k) (hk : k ≠ 0) (g : PG p k) (H : Root p k) :
    fp p k hk (Root.conj p k g H) = g • fp p k hk H := by
  refine fp_eq_of_fixes p k hp hq hk _ ?_
  intro u hu
  obtain ⟨t, ht, htu⟩ := (mem_Root_conj p k).mp hu
  rw [← htu]
  change (g * t * g⁻¹ : PG p k) • (g • fp p k hk H) = g • fp p k hk H
  calc (g * t * g⁻¹ : PG p k) • (g • fp p k hk H)
      = g • (t • (g⁻¹ • (g • fp p k hk H))) := by rw [mul_smul, mul_smul]
    _ = g • (t • fp p k hk H) := by rw [inv_smul_smul]
    _ = g • fp p k hk H := by rw [fp_fixes p k hk H t ht]

/-! ## The action of an automorphism on root subgroups -/

lemma Root.aut_conj (α : MulAut (PG p k)) (g : PG p k) (H : Root p k) :
    Root.aut p k α (Root.conj p k g H) = Root.conj p k (α g) (Root.aut p k α H) := by
  apply Subtype.ext
  simp only [Root.aut_val, Root.conj_val]
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, map_mul, map_inv]

lemma Root.aut_bijective (α : MulAut (PG p k)) : Function.Bijective (Root.aut p k α) := by
  refine ⟨fun H H' h => ?_, fun H => ⟨Root.aut p k α.symm H, ?_⟩⟩
  · have hval : (Root.aut p k α H).1 = (Root.aut p k α H').1 := congrArg Subtype.val h
    simp only [Root.aut_val] at hval
    exact Subtype.ext (Subgroup.map_injective α.injective hval)
  · apply Subtype.ext
    simp only [Root.aut_val]
    rw [Subgroup.map_map]
    have hcomp : (MulEquiv.toMonoidHom α).comp (MulEquiv.symm α).toMonoidHom =
        MonoidHom.id (PG p k) := by ext x; simp
    rw [hcomp, Subgroup.map_id]

/-! ## Surjectivity of `conjHom` -/

theorem conjHom_surjective (p k : ℕ) [Fact p.Prime] [Fintype (GaloisField p k)]
    (hp : Odd p) (hq : 5 ≤ p ^ k) [DecidableEq (GaloisField p k)] :
    Function.Surjective (Work.AUTL2.conjHom (GaloisField p k)) := by
  have hk : k ≠ 0 := by rintro rfl; simp at hq
  intro α
  have hbij : Function.Bijective (fp p k hk) :=
    ⟨fp_injective p k hp hq hk, fp_surjective p k hp hq hk⟩
  let fpEquiv : Root p k ≃ Pl p k := Equiv.ofBijective (fp p k hk) hbij
  have hfpEquiv : ∀ H : Root p k, fpEquiv H = fp p k hk H := fun H => rfl
  let αRoot : Root p k ≃ Root p k := Equiv.ofBijective (Root.aut p k α) (Root.aut_bijective p k α)
  have hαRoot : ∀ H : Root p k, αRoot H = Root.aut p k α H := fun H => rfl
  let Φ : Pl p k → Pl p k := fun x => fp p k hk (αRoot (fpEquiv.symm x))
  have hΦbij : Function.Bijective Φ := by
    have h1 : Function.Bijective (fp p k hk ∘ (αRoot ∘ fpEquiv.symm)) :=
      hbij.comp (αRoot.bijective.comp fpEquiv.symm.bijective)
    simpa [Φ, Function.comp_def] using h1
  let φ : Equiv.Perm (Pl p k) := Equiv.ofBijective Φ hΦbij
  have hφ_apply : ∀ x : Pl p k, φ x = fp p k hk (αRoot (fpEquiv.symm x)) := fun x => rfl
  have hkey : ∀ (g : PG p k) (x : Pl p k), φ (g • x) = (α g) • φ x := by
    intro g x
    set H : Root p k := fpEquiv.symm x with hH
    have hx : fp p k hk H = x := by
      have h1 := Equiv.apply_symm_apply fpEquiv x
      rw [hfpEquiv] at h1
      rw [hH]
      exact h1
    have hsymm : fpEquiv.symm (g • x) = Root.conj p k g H := by
      rw [Equiv.symm_apply_eq]
      rw [hfpEquiv, fp_conj p k hp hq hk g H, hx]
    rw [hφ_apply (g • x), hsymm, hαRoot, Root.aut_conj,
      fp_conj p k hp hq hk (α g) (Root.aut p k α H), hφ_apply x, hαRoot, ← hH]
  have hconj : ∀ g : PG p k,
      φ * (g : Equiv.Perm (Pl p k)) * φ⁻¹ = ((α g : PG p k) : Equiv.Perm (Pl p k)) := by
    intro g
    ext x
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    have h2 := hkey g (φ⁻¹ x)
    have h3 : φ (φ⁻¹ x) = x := Equiv.apply_symm_apply φ x
    rw [h3] at h2
    exact h2
  have hmap : (Work.AUTL2.pslImage (GaloisField p k)).map (MulAut.conj φ) =
      Work.AUTL2.pslImage (GaloisField p k) := by
    refine le_antisymm ?_ ?_
    · rintro y ⟨g, hg, rfl⟩
      change φ * g * φ⁻¹ ∈ Work.AUTL2.pslImage (GaloisField p k)
      have hmem : φ * g * φ⁻¹ = ((α ⟨g, hg⟩ : PG p k) : Equiv.Perm (Pl p k)) :=
        hconj ⟨g, hg⟩
      rw [hmem]
      exact (α ⟨g, hg⟩).2
    · intro y hy
      refine Subgroup.mem_map.mpr ⟨(α.symm ⟨y, hy⟩ : PG p k), (α.symm ⟨y, hy⟩).2, ?_⟩
      change φ * (((α.symm ⟨y, hy⟩ : PG p k)) : Equiv.Perm (Pl p k)) * φ⁻¹ = y
      rw [hconj (α.symm ⟨y, hy⟩), MulEquiv.apply_symm_apply]
  have hN : φ ∈ Subgroup.normalizer (Work.AUTL2.pslImage (GaloisField p k) : Set _) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap
  have hpg : φ ∈ Work.AUTL2.pgammaL (GaloisField p k) :=
    Work.AUTL2.Normalizer.le_pgammaL p k hp hq φ hN
  refine ⟨⟨φ, hpg⟩, ?_⟩
  apply MulEquiv.ext
  intro g
  apply Subtype.ext
  show φ * (g : Equiv.Perm (Pl p k)) * φ⁻¹ = ((α g : PG p k) : Equiv.Perm (Pl p k))
  exact hconj g

end Work.DSTR.M110
