import Mathlib
import Submission.Work.Fitting.Main
import Submission.Work.ThmF.ChV12.Fitting_cyclic_fpf
import Submission.Work.ThmF.ChV12.index_centralizer_le_totient
import Submission.Work.ThmF.ChV12.map_invariant_of_normal
import Submission.Work.ThmF.ChV12.mul_lt_two_pow_sub_one
import Submission.Work.ThmF.ChV12.natCard_ne_one

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV12.fitting_card_lt_centralizer` — the counting brick (Brick B)

`A` is a finite elementary abelian `2`-group and `D` a finite group of odd order acting
faithfully and transitively on `A ∖ {1}`.  If some nontrivial proper subgroup `W ≤ A` is
invariant under the Fitting subgroup `F(D)`, then

`|F(D)| < |C_D(F(D))|`,

i.e. the centralizer of the Fitting subgroup in `D` is strictly larger than the Fitting
subgroup itself (note `F(D) ≤ C_D(F(D))`: `F(D)` is cyclic by Brick A).

The proof is the orbit count of the note `NOTES_fitting_irreducible_of_transitive.md`, §3,
in a sharper form that avoids the partition of `A ∖ {1}` into conjugates:

* `F(D)` is cyclic and acts fixed-point-freely on `A ∖ {1}` (Brick A,
  `Work.ThmF.ChV12.Fitting_cyclic_fpf`);
* pick `U ≤ W` minimal among the nontrivial `F(D)`-invariant subgroups of `A`.  Then
  `|U| = 2^d`, `d ≥ 1`, `U` is `F(D)`-irreducible (`F(D)`-invariant subgroups of `U` are
  `⊥` or `U`), and the orbit of any `u ∈ U#` under `F(D)` is a free `F(D)`-orbit inside
  `U#`.  Hence `m := |F(D)| ≤ 2^d - 1`;
* since `U ≤ W ≠ ⊤`, some `D`-translate `U' = ρ e U` of `U` is different from `U`; it is
  again `F(D)`-invariant, and `U ⊓ U' = ⊥` because `U` is `F(D)`-irreducible.  Hence the
  product map `↥U × ↥U' → A` is injective and `2^{2d} ≤ |A| = 2^k`, i.e. `2d ≤ k`;
* `D → MulAut ↥F(D)` by conjugation has kernel `C_D(F(D))`, so
  `|D : C_D(F(D))| ≤ φ(m) ≤ m ≤ 2^d - 1`;
* transitivity gives `2^k - 1 = |A ∖ {1}| ≤ |D|`.

Combining: `|F(D)| · |D : C_D(F(D))| ≤ (2^d-1)^2 < 2^{2d} - 1 ≤ 2^k - 1 ≤ |D|`, and since
`|D| = |D : C_D(F(D))| · |C_D(F(D))|` this is `|F(D)| < |C_D(F(D))|`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Work.ThmF.ChV12

theorem fitting_card_lt_centralizer {A D : Type} [Group A] [Group D] [Finite A] [Finite D]
    (hA2 : ∀ x : A, x * x = 1) (hAc : ∀ x y : A, x * y = y * x)
    (hodd : Odd (Nat.card D)) (ρ : D →* MulAut A) (hfaith : Function.Injective ρ)
    (htrans : ∀ a b : A, a ≠ 1 → b ≠ 1 → ∃ d : D, ρ d a = b)
    (hW : ∃ W : Subgroup A, W ≠ ⊥ ∧ W ≠ ⊤ ∧
      (∀ t ∈ Work.Fitting.fitting D, ∀ x : A, x ∈ W → ρ t x ∈ W)) :
    Nat.card ↥(Work.Fitting.fitting D) <
      Nat.card ↥(Subgroup.centralizer (Work.Fitting.fitting D : Set D)) := by
  classical
  -- the Fitting subgroup `F` of `D`, its centralizer `C`, and Brick A
  let F : Subgroup D := Work.Fitting.fitting D
  let C : Subgroup D := Subgroup.centralizer (F : Set D)
  haveI hFnorm : F.Normal := by
    change (Work.Fitting.fitting D).Normal
    exact Work.Fitting.normal_sSup (S := Work.Fitting.fittingSet D) (fun N hN => hN.1)
  obtain ⟨hFcyc, hFfpf⟩ := Fitting_cyclic_fpf hA2 hAc hodd ρ hfaith htrans
  haveI hFcycI : IsCyclic ↥F := hFcyc
  obtain ⟨W, hWne, hWtop, hWin⟩ := hW
  -- ## 1. a minimal nontrivial `F`-invariant subgroup `U ≤ W`
  let S : Set (Subgroup A) := {X | X ≤ W ∧ X ≠ ⊥ ∧ ∀ t ∈ F, ∀ x : A, x ∈ X → ρ t x ∈ X}
  have hSne : S.Nonempty := ⟨W, le_rfl, hWne, hWin⟩
  obtain ⟨U, hUmin⟩ := (Set.toFinite S).exists_minimal hSne
  have hUleW : U ≤ W := hUmin.1.1
  have hUne : U ≠ ⊥ := hUmin.1.2.1
  have hUinv : ∀ t ∈ F, ∀ x : A, x ∈ U → ρ t x ∈ U := hUmin.1.2.2
  have hUirr : ∀ X : Subgroup A, X ≤ U → X ≠ ⊥ →
      (∀ t ∈ F, ∀ x : A, x ∈ X → ρ t x ∈ X) → X = U := by
    intro X hXle hXne hXinv
    exact le_antisymm hXle (hUmin.2 ⟨hXle.trans hUleW, hXne, hXinv⟩ hXle)
  -- ## 2. `|U| = 2^d`, `d ≥ 1`, and a nontrivial element `a₀ ∈ U`
  obtain ⟨d, hdU⟩ := card_eq_two_pow_of_mul_self_eq_one (A := ↥U)
    (fun x => Subtype.ext (by simpa using hA2 (x : A)))
  have htwo : 1 < Nat.card ↥U := (Subgroup.one_lt_card_iff_ne_bot U).mpr hUne
  have hd1 : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · rw [h] at hdU
      rw [pow_zero] at hdU
      omega
    · exact h
  obtain ⟨a₀, ha₀U, ha₀ne⟩ : ∃ a : A, a ∈ U ∧ a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hUne ((Subgroup.eq_bot_iff_forall U).mpr hcon)
  -- ## 3. `|F| ≤ |U| - 1 = 2^d - 1`: the `F`-orbit of `a₀` is free
  have hm_le : Nat.card ↥F ≤ 2 ^ d - 1 := by
    have hne1 : ∀ t : ↥F, (ρ t.1 a₀ : A) ≠ 1 := by
      intro t h
      exact ha₀ne ((ρ t.1).injective (by rw [h, map_one]))
    have hcardU : Nat.card {x : ↥U // x ≠ 1} = 2 ^ d - 1 := by
      rw [natCard_ne_one (G := ↥U), hdU]
    rw [← hcardU]
    let f : ↥F → {x : ↥U // x ≠ 1} := fun t =>
      ⟨⟨ρ t.1 a₀, hUinv t.1 t.2 a₀ ha₀U⟩,
        fun h => hne1 t (by simpa using congrArg Subtype.val h)⟩
    refine Nat.card_le_card_of_injective f ?_
    intro s t hst
    have hval : (ρ s.1 a₀ : A) = (ρ t.1 a₀ : A) := by
      have h := congrArg (fun z : {x : ↥U // x ≠ 1} => ((z.1 : ↥U) : A)) hst
      simpa [f] using h
    have hfix : ρ ((t⁻¹ * s).1) a₀ = a₀ := by
      have hmul : ρ ((t⁻¹ * s).1) a₀ = ((ρ t.1)⁻¹ * ρ s.1) a₀ := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
      rw [hmul, MulAut.mul_apply, hval, MulAut.inv_apply]
      exact MulEquiv.symm_apply_apply (ρ t.1) a₀
    have hone : t⁻¹ * s = 1 := by
      by_contra hne
      refine ha₀ne (hFfpf ((t⁻¹ * s).1) ?_ (fun h => hne (Subtype.ext h)) a₀ hfix)
      exact (t⁻¹ * s).2
    exact (inv_mul_eq_one.mp hone).symm
  -- ## 4. `|A| = 2^k` and `|A ∖ {1}| = 2^k - 1 ≤ |D|`
  obtain ⟨k, hk⟩ := card_eq_two_pow_of_mul_self_eq_one (A := A) hA2
  have hDge : 2 ^ k - 1 ≤ Nat.card D := by
    have hcard : Nat.card {x : A // x ≠ 1} = 2 ^ k - 1 := by
      rw [natCard_ne_one (G := A), hk]
    rw [← hcard]
    let g : D → {x : A // x ≠ 1} := fun e =>
      ⟨ρ e a₀, fun h => ha₀ne ((ρ e).injective (by rw [h, map_one]))⟩
    refine Nat.card_le_card_of_surjective g ?_
    intro x
    obtain ⟨e, he⟩ := htrans a₀ x.1 ha₀ne x.2
    exact ⟨e, Subtype.ext he⟩
  -- ## 5. a second, distinct `F`-invariant translate `U'` of `U`, with `U ⊓ U' = ⊥`
  obtain ⟨a₁, ha₁W⟩ : ∃ a : A, a ∉ W := by
    by_contra hcon
    push Not at hcon
    exact hWtop ((Subgroup.eq_top_iff' W).mpr hcon)
  have ha₁ne : a₁ ≠ 1 := fun h => ha₁W (h ▸ W.one_mem)
  obtain ⟨e, he⟩ := htrans a₀ a₁ ha₀ne ha₁ne
  let U' : Subgroup A := U.map (ρ e).toMonoidHom
  have hU'inv : ∀ t ∈ F, ∀ x : A, x ∈ U' → ρ t x ∈ U' := map_invariant_of_normal ρ hUinv e
  have hU'int : U ⊓ U' = ⊥ := by
    have hIntInv : ∀ t ∈ F, ∀ x : A, x ∈ U ⊓ U' → ρ t x ∈ U ⊓ U' :=
      fun t ht x hx => ⟨hUinv t ht x hx.1, hU'inv t ht x hx.2⟩
    by_contra hne
    have hEq : U ⊓ U' = U := hUirr (U ⊓ U') inf_le_left hne hIntInv
    have hle : U ≤ U' := hEq ▸ inf_le_right
    have hU'card : Nat.card ↥U' = Nat.card ↥U := by
      show Nat.card ↥(U.map (ρ e).toMonoidHom) = Nat.card ↥U
      exact Subgroup.card_map_of_injective (ρ e).injective
    have hUU' : U = U' := Subgroup.eq_of_le_of_card_ge hle (le_of_eq hU'card)
    have ha₁U' : a₁ ∈ U' := by
      refine Subgroup.mem_map.mpr ⟨a₀, ha₀U, ?_⟩
      exact he
    have ha₁U : a₁ ∈ U := by rw [hUU']; exact ha₁U'
    exact ha₁W (hUleW ha₁U)
  -- ## 6. `2^{2d} ≤ |U| · |U'| ≤ |A| = 2^k`, so `2d ≤ k`
  have hkd : 2 * d ≤ k := by
    have hU'card : Nat.card ↥U' = 2 ^ d := by
      rw [← hdU]
      show Nat.card ↥(U.map (ρ e).toMonoidHom) = Nat.card ↥U
      exact Subgroup.card_map_of_injective (ρ e).injective
    have hle : Nat.card ↥U * Nat.card ↥U' ≤ Nat.card A := by
      rw [← Nat.card_prod]
      exact Nat.card_le_card_of_injective _
        (Subgroup.mul_injective_of_disjoint (disjoint_iff.mpr hU'int))
    have h2 : 2 ^ d * 2 ^ d ≤ 2 ^ k := by
      have h : Nat.card ↥U * Nat.card ↥U' ≤ Nat.card A := hle
      rw [hdU, hU'card, hk] at h
      exact h
    have h3 : 2 ^ (2 * d) ≤ 2 ^ k := by
      rw [two_mul, pow_add]
      exact h2
    exact (Nat.pow_le_pow_iff_right (by norm_num : (1 : ℕ) < 2)).mp h3
  -- ## 7. the index of `C_D(F)` is at most `φ(|F|) ≤ |F| ≤ 2^d - 1`
  have ht_le : C.index ≤ Nat.card ↥F :=
    le_trans (index_centralizer_le_totient F hFcyc) (Nat.totient_le (Nat.card ↥F))
  -- ## 8. endgame
  have hmul_lt : Nat.card ↥F * C.index < 2 ^ k - 1 :=
    mul_lt_two_pow_sub_one hd1 hkd hm_le ht_le
  have hDsplit : C.index * Nat.card ↥C = Nat.card D := Subgroup.index_mul_card C
  have hgoal : Nat.card ↥F * C.index < Nat.card ↥C * C.index := by
    rw [Nat.mul_comm (Nat.card ↥C) C.index, hDsplit]
    exact lt_of_lt_of_le hmul_lt hDge
  exact Nat.lt_of_mul_lt_mul_right hgoal

end Work.ThmF.ChV12
