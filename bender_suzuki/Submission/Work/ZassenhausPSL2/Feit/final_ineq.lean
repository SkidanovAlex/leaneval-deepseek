import Mathlib
import Submission.Work.ZassenhausPSL2.Defs
import Submission.Work.ZassenhausPSL2.Basic
import Submission.Work.CharCore.Defs
import Submission.Work.Induction.Defs
import Submission.Work.Coherence.Defs
import Submission.Work.CharCore.Basic
import Submission.Work.CharCore.CFun
import Submission.Work.CharCore.irr_orthonormal
import Submission.Work.CharCore.classFun_eq_sum_irr
import Submission.Work.CharCore.classFun_eq_zero_of_orthogonal
import Submission.Work.CharCore.isChar_iff
import Submission.Work.CharCore.isChar_iff_exists_nat_coeffs
import Submission.Work.CharCore.isChar_mul
import Submission.Work.CharCore.isChar_character
import Submission.Work.CharCore.mem_Irr_iff_fdrep
import Submission.Work.CharCore.sum_irr_degree_sq
import Submission.Work.CharCore.principalChar_mem_Irr
import Submission.Work.CharCore.star_Irr
import Submission.Work.CharCore.star_char
import Submission.Work.CharCore.linear_char_iff_deg_one
import Submission.Work.CharCore.vchar_norm_one
import Submission.Work.Induction.Basic
import Submission.Work.Induction.frobenius_reciprocity
import Submission.Work.Induction.isChar_indFun
import Submission.Work.Induction.isClassFun_indFun
import Submission.Work.Induction.indFun_apply_one
import Submission.Work.ThmG.rankOne_index
import Submission.Work.ThmF.Setup
import Submission.Work.ZassenhausPSL2.ZData.three_le_card_twoPoint
import Submission.Work.ZassenhausPSL2.ZData.t_conj_eq_inv
import Submission.Work.ZassenhausPSL2.Feit.excl_aux
import Submission.Work.ZassenhausPSL2.Feit.excl_degree_support
import Submission.Work.ZassenhausPSL2.Feit.not_excl_linear
import Submission.Work.ZassenhausPSL2.Feit.card_excl
import Submission.Work.ZassenhausPSL2.Feit.final_card_lin
import Submission.Work.ZassenhausPSL2.Feit.cfInner_indFun_excl_self
import Submission.Work.ZassenhausPSL2.Feit.cfInner_indFun_linear_self_notreal
import Submission.Work.ZassenhausPSL2.Feit.FinalMackey
import Submission.Work.ThmG2.cfInner_indFun_self_twoDoubleCoset
import Submission.Work.ZassenhausPSL2.Feit.linear_of_trivial_on_Q

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausPSL2.Feit

/-!
# `Work.ZassenhausPSL2.Feit.final_ineq` (Feit's leaf F7)

In a split rank-one Zassenhaus configuration `H = Q ⋊ D` inside a finite simple group `G`
(`D = twoPoint H t = H ∩ Hᵗ`, `Q` an abelian `2`-group), if `χ₁ ∈ 𝒮 = excludingKernel H Q`
and `ξ ∈ Irr G` restricts to `χ₁` on `H`, then Feit's inequality

`2 + (d - 1)·(m + 1) ≤ 2·d²`,   `d = |D|`, `m = |Q|`

holds.

## The argument

Write `d = |D|`, `m = |Q|` and `Ξ = ξ ξ̄` (pointwise product with the conjugate character
`star ξ`).  Then `Ξ` is a character of `G` of degree `d²`, containing the principal character
exactly once, and `ξ|_H = χ₁`.

* For every irreducible character `λ` of `H` which is trivial on `Q`, Frobenius reciprocity and
  the vanishing of `χ₁` off `Q` give `⟨Ξ, Ind_H^G λ⟩ = ⟨λ, χ₁ χ̄₁⟩_H = ⟨χ₁, χ₁⟩_H = 1`; so
  `Ind_H^G λ` is a constituent of `Ξ - 1` with multiplicity `1`.
  When `λ ≠ 1` and `λ ≠ λ̄`, `Ind_H^G λ` is *irreducible* of degree `m + 1`
  (`cfInner_indFun_linear_self_notreal`, assembled in `final_indFun_lin_mem_Irr_local`), and
  `Ind_H^G λ ≠ Ind_H^G μ` for distinct pairs `{λ, λ̄}` (`final_linear_ne_local`, from the
  polarised Mackey formula `mackeyPolar`).
* There are `d - 1` non-trivial such `λ`, i.e. `(d-1)/2` distinct pairs `{λ, λ̄}`
  (`final_card_lin`), so `Ξ - 1` contains at least `(d-1)/2` distinct irreducible characters of
  degree `m + 1`; hence `d² - 1 ≥ (d-1)(m+1)/2`, which is the claim.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

open Classical

/-- A non-trivial irreducible character of `H` which is trivial on `Q` is not real-valued: if
`λ = λ̄` then `λ` is a homomorphism to `{±1}` trivial on `Q`, hence trivial on all of `H`
because `H/Q` has odd order (`Q.subgroupOf H` has odd index), so `λ = 1`.

This is what allows the characters `Ind_H^G λ` of `L*` to be irreducible
(`cfInner_indFun_linear_self_notreal`) and pairwise orthogonal (`final_linear_ne`). -/
private theorem ne_conj_of_ne_one {G : Type} [Group G] [Fintype G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hz : Submission.Blueprint.IsZassenhaus H)
    (h2 : IsPGroup 2 Q) (hab : Submission.Blueprint.IsAbelianSubgroup Q) {lc : H → ℂ}
    (hlc : lc ∈ Work.CharCore.Irr H) (hlcQ : ∀ x : H, (x : G) ∈ Q → lc x = 1)
    (hne : lc ≠ fun _ : H => 1) :
    lc ≠ fun x : H => starRingEnd ℂ (lc x) := by
  classical
  intro hconj
  refine hne (funext fun x => ?_)
  -- `lc` is linear
  obtain ⟨φ, hφ⟩ := linear_of_trivial_on_Q h hz h2 hab hlc hlcQ
  have hmul : ∀ a b : H, lc (a * b) = lc a * lc b := by
    intro a b
    rw [hφ (a * b), map_mul, Units.val_mul, hφ a, hφ b]
  have hpow : ∀ (a : H) (k : ℕ), lc (a ^ k) = (lc a) ^ k := by
    intro a k
    induction k with
    | zero => rw [pow_zero, pow_zero, hlcQ 1 Q.one_mem]
    | succ n ih => rw [pow_succ, hmul, ih, pow_succ]
  -- every value has square one, because `lc x = conj (lc x) = lc x⁻¹ = (lc x)⁻¹`
  have hsq : ∀ y : H, lc y * lc y = 1 := by
    intro y
    have hy : lc y = starRingEnd ℂ (lc y) := congrFun hconj y
    rw [Work.CharCore.star_Irr lc hlc y, hφ y⁻¹, map_inv, Units.val_inv_eq_inv_val, hφ y] at hy
    have hne : (↑(φ y) : ℂ) ≠ 0 := Units.ne_zero (φ y)
    have h4 := congrArg (fun z : ℂ => z * (↑(φ y) : ℂ)) hy
    rw [inv_mul_cancel₀ hne] at h4
    rw [hφ y]
    exact h4
  -- `x ^ [H : Q] ∈ Q`, and `[H : Q]` is odd
  have hQn : (Q.subgroupOf H).Normal := qSubgroupOf_normal h
  have hodd : Odd (Q.subgroupOf H).index := by
    rw [index_subgroupOf_Q h]
    exact Work.ZassenhausPSL2.dStab_odd H t h.stronglyEmbedded h.not_mem
  obtain ⟨k, hk⟩ := hodd
  have hmem : ((x ^ (Q.subgroupOf H).index : H) : G) ∈ Q :=
    Subgroup.mem_subgroupOf.mp (Subgroup.pow_index_mem (Q.subgroupOf H) x)
  have h1 : (lc x) ^ (Q.subgroupOf H).index = 1 := by
    rw [← hpow x (Q.subgroupOf H).index]
    exact hlcQ (x ^ (Q.subgroupOf H).index) hmem
  have h3 : lc x = (lc x) ^ (2 * k + 1) := by
    rw [pow_succ, pow_mul]
    rw [show (lc x) ^ 2 = lc x * lc x from pow_two (lc x), hsq x, one_pow, one_mul]
  rw [h3, ← hk]
  exact h1

/-- **The key inner-product computation.**  For `χ₁ ∈ 𝒮` and `ξ ∈ Irr G` with `ξ|_H = χ₁`, and
any irreducible character `λ` of `H` which is trivial on `Q`,

`⟨ξ ξ̄, Ind_H^G λ⟩_G = 1`.

Indeed, by Frobenius reciprocity (with the conjugate symmetry of `cfInner`) this is
`⟨λ, χ₁ χ̄₁⟩_H`; `χ₁` vanishes off `Q` while `λ = 1` on `Q`, so the sum `∑_{x ∈ H} λ x·|χ₁ x|²`
collapses to `∑_{x ∈ H} |χ₁ x|²`, i.e. to `|H|·⟨χ₁, χ₁⟩_H = |H|`. -/
private theorem cfInner_mul_star_indFun_linear {G : Type} [Group G] [Fintype G]
    {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hz : Submission.Blueprint.IsZassenhaus H)
    (h2 : IsPGroup 2 Q) (hab : Submission.Blueprint.IsAbelianSubgroup Q)
    {χ₁ : H → ℂ} (hχ₁ : χ₁ ∈ Submission.Blueprint.excludingKernel H Q)
    {ξ : G → ℂ} (hξ : ξ ∈ Work.CharCore.Irr G) (hres : ∀ x : H, ξ x = χ₁ x)
    {lc : H → ℂ}
    (hlcQ : ∀ x : H, (x : G) ∈ Q → lc x = 1) :
    Work.CharCore.cfInner (ξ * star ξ) (Work.Induction.indFun H lc) = 1 := by
  classical
  obtain ⟨hχ₁Irr, -⟩ := mem_excludingKernel_iff.mp hχ₁
  have hvanish : ∀ x : H, (x : G) ∉ Q → χ₁ x = 0 :=
    (excl_degree_support h hz h2 hab hχ₁).2
  have hcard : (Fintype.card ↥H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  -- the auxiliary inner product `⟨λ, χ₁ χ̄₁⟩_H = 1`
  have hkey : Work.CharCore.cfInner lc (χ₁ * fun x : H => starRingEnd ℂ (χ₁ x)) = 1 := by
    rw [Work.CharCore.cfInner_conj_symm]
    have hkey2 : Work.CharCore.cfInner (χ₁ * fun x : H => starRingEnd ℂ (χ₁ x)) lc = 1 := by
      rw [Work.CharCore.cfInner_apply]
      simp only [Pi.mul_apply]
      have hterm : ∀ x : H, (χ₁ x * starRingEnd ℂ (χ₁ x)) * starRingEnd ℂ (lc x)
          = χ₁ x * starRingEnd ℂ (χ₁ x) := by
        intro x
        by_cases hx : (x : G) ∈ Q
        · rw [hlcQ x hx]; simp
        · rw [hvanish x hx]; simp
      rw [Finset.sum_congr rfl fun x _ => hterm x]
      rw [show (∑ x : H, χ₁ x * starRingEnd ℂ (χ₁ x))
          = (Fintype.card ↥H : ℂ) * Work.CharCore.cfInner χ₁ χ₁ from by
        rw [Work.CharCore.cfInner_apply, ← mul_assoc, mul_inv_cancel₀ hcard, one_mul]]
      rw [Work.CharCore.irr_orthonormal χ₁ χ₁ hχ₁Irr hχ₁Irr, if_pos rfl, mul_one]
      exact inv_mul_cancel₀ hcard
    rw [hkey2]; simp
  -- Frobenius reciprocity
  have hres' : Work.Induction.resFun H (ξ * star ξ)
      = χ₁ * fun x : H => starRingEnd ℂ (χ₁ x) := by
    funext x
    show ξ x * (star ξ) x = χ₁ x * starRingEnd ℂ (χ₁ x)
    rw [Pi.star_apply, ← starRingEnd_apply, hres x]
  have hmain : Work.CharCore.cfInner (Work.Induction.indFun H lc) (ξ * star ξ) = 1 := by
    have hclassξ : Work.CharCore.IsClassFun ξ := Work.CharCore.isClassFun_of_mem_Irr hξ
    have hclassξc : Work.CharCore.IsClassFun (star ξ) := by
      rw [show star ξ = fun g => starRingEnd ℂ (ξ g) from
        funext fun g => Pi.star_apply ξ g]
      exact hclassξ.conj
    rw [Work.Induction.frobenius_reciprocity H lc (ξ * star ξ) (hclassξ.mul hclassξc), hres', hkey]
  rw [Work.CharCore.cfInner_conj_symm, hmain]; simp

/-- `ξ ξ̄` is a character of `G`: `ξ` is the character of a simple finite dimensional
representation `V`, and `star ξ = fun g => ξ g⁻¹` is the character of the dual representation
(`Representation.char_dual`). -/
private theorem isChar_mul_star {G : Type} [Group G] [Fintype G] {ξ : G → ℂ}
    (hξ : ξ ∈ Work.CharCore.Irr G) :
    Work.CharCore.IsChar (ξ * star ξ) := by
  classical
  obtain ⟨V, -, hchar⟩ := (Work.CharCore.mem_Irr_iff_fdrep ξ).mp hξ
  have hstar : star ξ = (Representation.dual V.ρ).character := by
    funext g
    rw [Pi.star_apply, ← starRingEnd_apply, Work.CharCore.star_Irr ξ hξ g, ← hchar]
    exact (Representation.char_dual V.ρ g).symm
  rw [hstar]
  exact Work.CharCore.isChar_mul (Work.CharCore.IsChar.of_mem_Irr hξ)
    (Work.CharCore.isChar_character (Representation.dual V.ρ))

/-- `⟨ξ ξ̄, 1_G⟩_G = ⟨ξ, ξ⟩_G = 1`. -/
private theorem cfInner_mul_star_one {G : Type} [Group G] [Fintype G] {ξ : G → ℂ}
    (hξ : ξ ∈ Work.CharCore.Irr G) :
    Work.CharCore.cfInner (ξ * star ξ) (fun _ : G => (1 : ℂ)) = 1 := by
  classical
  have hself : Work.CharCore.cfInner ξ ξ = 1 := by
    rw [Work.CharCore.irr_orthonormal ξ ξ hξ hξ, if_pos rfl]
  rw [Work.CharCore.cfInner_conj_symm]
  have h1 : Work.CharCore.cfInner (fun _ : G => (1 : ℂ)) (ξ * star ξ) = 1 := by
    rw [Work.CharCore.cfInner_apply]
    have hterm : ∀ g : G, (1 : ℂ) * starRingEnd ℂ ((ξ * star ξ) g)
        = ξ g * starRingEnd ℂ (ξ g) := by
      intro g
      simp only [Pi.mul_apply, Pi.star_apply, one_mul, map_mul, starRingEnd_apply, star_star]
      ring
    rw [Finset.sum_congr rfl fun g _ => hterm g, ← Work.CharCore.cfInner_apply, hself]
  rw [h1]; simp

/-- The sum of a multiplicative complex function on a finite group which is not identically
`1` vanishes: multiplying the sum by a value `≠ 1` permutes the index set. -/
private theorem sum_eq_zero_of_mul_map {X : Type} [Group X] [Fintype X] {f : X → ℂ}
    (hmul : ∀ x y : X, f (x * y) = f x * f y) (hne : ∃ x : X, f x ≠ 1) :
    ∑ x : X, f x = 0 := by
  obtain ⟨a, ha⟩ := hne
  have h1 : (∑ x : X, f (a * x)) = ∑ x : X, f x :=
    Fintype.sum_equiv (Equiv.mulLeft a) (fun x => f (a * x)) (fun x => f x) (fun x => rfl)
  have h2 : (∑ x : X, f (a * x)) = f a * ∑ x : X, f x := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => hmul a x
  have h3 : (f a - 1) * (∑ x : X, f x) = 0 := by
    rw [sub_mul, one_mul, ← h2, h1, sub_self]
  exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr ha)

/-- **Off-diagonal orthogonality of the induced linear characters.**  For two irreducible
characters `lc ≠ lc'` of `H`, both trivial on `Q` and with `lc' ≠ lc⁻¹ = conj lc`, the induced
characters of `G` are orthogonal.  This is Mackey's formula on the two double cosets `H` and
`H t H`: the value at `H` is `⟨lc, lc'⟩_H = 0`, and the correction term is `|D|⁻¹` times the
sum of the multiplicative function `lc · lc'` over `D`, which vanishes because `lc · lc'` is
not identically `1` (`t` inverts `D`). -/
private theorem final_linear_ne_local {G : Type} [Group G] [Fintype G] {H Q : Subgroup G}
    {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hz : Submission.Blueprint.IsZassenhaus H)
    (h2 : IsPGroup 2 Q) (hab : Submission.Blueprint.IsAbelianSubgroup Q) {lc lc' : H → ℂ}
    (hlc : lc ∈ Work.CharCore.Irr H) (hlc' : lc' ∈ Work.CharCore.Irr H)
    (hlcQ : ∀ x : H, (x : G) ∈ Q → lc x = 1)
    (hlc'Q : ∀ x : H, (x : G) ∈ Q → lc' x = 1)
    (hne1 : lc' ≠ lc) (hne2 : lc' ≠ fun x => starRingEnd ℂ (lc x)) :
    Work.CharCore.cfInner (Work.Induction.indFun H lc) (Work.Induction.indFun H lc') = 0 := by
  classical
  -- `Q ≠ ⊥`, so `t` inverts `D`
  have hQ : Q ≠ ⊥ := by
    intro hbot
    have htwo : Submission.Blueprint.twoPoint H t = H := by
      have hs : Q ⊔ Submission.Blueprint.twoPoint H t = H := h.sup_eq
      rw [hbot, bot_sup_eq] at hs
      exact hs
    have hodd : Odd (Nat.card (Submission.Blueprint.twoPoint H t)) :=
      Work.ZassenhausPSL2.dStab_odd H t h.stronglyEmbedded h.not_mem
    rw [htwo] at hodd
    exact (Nat.not_odd_iff_even.mpr h.stronglyEmbedded.2.1) hodd
  have hinv : ∀ d : G, d ∈ Submission.Blueprint.twoPoint H t → t * d * t = d⁻¹ :=
    Work.ZassenhausPSL2.ZData.t_conj_eq_inv H Q t h hz hQ h2
  have ht : t * t = 1 := Work.ZassenhausPSL2.t_mul_t h
  obtain ⟨φ, hφ⟩ := linear_of_trivial_on_Q h hz h2 hab hlc hlcQ
  obtain ⟨φ', hφ'⟩ := linear_of_trivial_on_Q h hz h2 hab hlc' hlc'Q
  -- the geometry of the split rank-one datum
  have hcover : ∀ g : G, g ∈ H ∨ ∃ a b : H, g = (a : G) * t * (b : G) := by
    intro g
    by_cases hg : g ∈ H
    · exact Or.inl hg
    · obtain ⟨p, hp, -⟩ := Work.ZassenhausPSL2.exists_unique_decomp (Q := Q) h hg
      exact Or.inr ⟨p.1, ⟨p.2, h.le p.2.2⟩, hp.symm⟩
  have hDmap : ∀ d : ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom : Subgroup G),
      (MulAut.conj t) (d : G) ∈ (H ⊓ H.map (MulAut.conj t).toMonoidHom : Subgroup G) := by
    intro d
    have h1 : (MulAut.conj t) (d : G) = t * (d : G) * t := by
      rw [MulAut.conj_apply, Work.ZassenhausPSL2.t_inv h]
    rw [h1]
    exact Work.ZassenhausPSL2.dStab_conj_mem h d.2
  have hclc : Work.CharCore.IsClassFun lc := Work.CharCore.isClassFun_of_mem_Irr hlc
  have hclc' : Work.CharCore.IsClassFun lc' := Work.CharCore.isClassFun_of_mem_Irr hlc'
  have hform := mackeyPolar (H := H) (t := t) ht h.not_mem hcover hDmap lc lc' hclc hclc'
  -- the `H` double coset contributes `0`
  have hH0 : Work.CharCore.cfInner lc lc' = 0 := by
    rw [Work.CharCore.irr_orthonormal lc lc' hlc hlc']
    exact if_neg fun hh => hne1 hh.symm
  -- the `H t H` double coset contributes `0`
  have hsum : (∑ d : ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom : Subgroup G),
      lc ⟨(d : G), (Subgroup.mem_inf.mp d.2).1⟩ *
        star (lc' ⟨(MulAut.conj t) (d : G), (Subgroup.mem_inf.mp (hDmap d)).1⟩)) = 0 := by
    have hstar : ∀ d : ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom : Subgroup G),
        star (lc' ⟨(MulAut.conj t) (d : G), (Subgroup.mem_inf.mp (hDmap d)).1⟩)
          = lc' ⟨(d : G), (Subgroup.mem_inf.mp d.2).1⟩ := by
      intro d
      have hy : (⟨(MulAut.conj t) (d : G), (Subgroup.mem_inf.mp (hDmap d)).1⟩ : ↥H)⁻¹
          = ⟨(d : G), (Subgroup.mem_inf.mp d.2).1⟩ := by
        apply Subtype.ext
        change ((MulAut.conj t) (d : G))⁻¹ = (d : G)
        rw [MulAut.conj_apply, Work.ZassenhausPSL2.t_inv h, hinv (d : G) d.2, inv_inv]
      rw [← starRingEnd_apply, Work.CharCore.star_Irr lc' hlc' _, hy]
    rw [Finset.sum_congr rfl fun d _ => by rw [hstar d]]
    refine sum_eq_zero_of_mul_map (f := fun d :
        ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom : Subgroup G) =>
      lc ⟨(d : G), (Subgroup.mem_inf.mp d.2).1⟩ *
        lc' ⟨(d : G), (Subgroup.mem_inf.mp d.2).1⟩) ?_ ?_
    · intro x y
      have hxy : (⟨((x * y : ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom : Subgroup G)) : G),
            (Subgroup.mem_inf.mp (x * y).2).1⟩ : ↥H)
          = ⟨(x : G), (Subgroup.mem_inf.mp x.2).1⟩ *
              ⟨(y : G), (Subgroup.mem_inf.mp y.2).1⟩ := by
        apply Subtype.ext
        rfl
      simp only [hxy, hφ, hφ', map_mul, Units.val_mul]
      ring
    · by_contra hcon
      push_neg at hcon
      apply hne2
      funext b
      obtain ⟨d, q, hdq⟩ := Work.ZassenhausPSL2.mem_eq_dStab_mul_Q h b
      set dH : ↥H := ⟨(d : G), (Subgroup.mem_inf.mp d.2).1⟩ with hdH
      set qH : ↥H := ⟨(q : G), h.le q.2⟩ with hqH
      have hb_eq : b = dH * qH := by
        apply Subtype.ext
        rw [Subgroup.coe_mul, hdH, hqH]
        exact hdq.symm
      have hφq : (φ qH : ℂ) = 1 := by
        have h1 : lc qH = 1 := hlcQ qH (by simpa [hqH] using q.2)
        rwa [hφ qH] at h1
      have hφ'q : (φ' qH : ℂ) = 1 := by
        have h1 : lc' qH = 1 := hlc'Q qH (by simpa [hqH] using q.2)
        rwa [hφ' qH] at h1
      have hpd : lc dH * lc' dH = 1 := by
        simpa only [← hdH] using hcon ⟨(d : G), d.2⟩
      have hst : star (lc dH) = (lc dH)⁻¹ := by
        rw [← starRingEnd_apply, Work.CharCore.star_Irr lc hlc dH, hφ dH⁻¹, map_inv,
          Units.val_inv_eq_inv_val, hφ dH]
      have hlc'b : lc' b = lc' dH := by
        rw [hb_eq, hφ' (dH * qH), map_mul, Units.val_mul, hφ'q, mul_one, ← hφ' dH]
      have hlcb : lc b = lc dH := by
        rw [hb_eq, hφ (dH * qH), map_mul, Units.val_mul, hφq, mul_one, ← hφ dH]
      calc lc' b = lc' dH := hlc'b
        _ = (lc dH)⁻¹ := eq_inv_of_mul_eq_one_right hpd
        _ = star (lc dH) := hst.symm
        _ = star (lc b) := by rw [hlcb]
        _ = starRingEnd ℂ (lc b) := by rw [starRingEnd_apply]
  rw [hform, hH0, hsum, mul_zero, add_zero]

/-- **Irreducibility of the induced linear character.**  For `lc ∈ Irr H` trivial on `Q` and
non-real (`lc ≠ conj lc`), `Ind_H^G lc` is an irreducible character of `G`: it is a character
(`Work.Induction.isChar_indFun`) of norm `1`
(`cfInner_indFun_linear_self_notreal`), and a norm-one character is `±` an irreducible;
the sign `-` is excluded because `Ind_H^G lc` has positive value `|G : H|` at the identity. -/
private theorem final_indFun_lin_mem_Irr_local {G : Type} [Group G] [Fintype G]
    {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hz : Submission.Blueprint.IsZassenhaus H)
    (h2 : IsPGroup 2 Q) (hab : Submission.Blueprint.IsAbelianSubgroup Q) {lc : H → ℂ}
    (hlc : lc ∈ Work.CharCore.Irr H) (hlcQ : ∀ x : H, (x : G) ∈ Q → lc x = 1)
    (hne : lc ≠ fun x => starRingEnd ℂ (lc x)) :
    Work.Induction.indFun H lc ∈ Work.CharCore.Irr G := by
  classical
  have hchar : Work.CharCore.IsChar (Work.Induction.indFun H lc) :=
    Work.Induction.isChar_indFun (Work.CharCore.IsChar.of_mem_Irr hlc)
  have hnorm : Work.CharCore.cfInner (Work.Induction.indFun H lc)
      (Work.Induction.indFun H lc) = 1 :=
    @cfInner_indFun_linear_self_notreal G _ _ H Q (inferInstance) t h hz h2 hab lc hlc hlcQ hne
  obtain ⟨χ, hχ, hcase⟩ :=
    Work.CharCore.vchar_norm_one (Work.CharCore.IsChar.toVChar hchar) hnorm
  rcases hcase with hh | hh
  · rw [hh]; exact hχ
  · exfalso
    have h1 := congrFun hh 1
    rw [Work.Induction.indFun_apply_one] at h1
    have hlc1 : lc 1 = 1 := hlcQ 1 Q.one_mem
    rw [hlc1, mul_one, Pi.neg_apply] at h1
    rw [Work.CharCore.irrDeg_spec hχ] at h1
    have h3 : ((Work.CharCore.irrDeg χ + H.index : ℕ) : ℂ) = 0 := by
      rw [Nat.cast_add, h1]; ring
    have h4 : Work.CharCore.irrDeg χ + H.index = 0 := Nat.cast_eq_zero.mp h3
    have h5 : 0 < H.index := by
      apply Nat.pos_of_ne_zero
      intro h0
      have hcard := Subgroup.index_mul_card H
      rw [h0, zero_mul] at hcard
      have hGN : Nat.card G ≠ 0 := by
        rw [Nat.card_eq_fintype_card]
        exact Fintype.card_ne_zero
      exact hGN hcard.symm
    omega

theorem final_ineq {G : Type} [Group G] [Fintype G] {H Q : Subgroup G} {t : G}
    [IsSimpleGroup G] (h : Submission.Blueprint.IsSplitRankOne H Q t)
    (hz : Submission.Blueprint.IsZassenhaus H) (h2 : IsPGroup 2 Q)
    (hab : Submission.Blueprint.IsAbelianSubgroup Q) {χ₁ : H → ℂ}
    (hχ₁ : χ₁ ∈ Submission.Blueprint.excludingKernel H Q) {ξ : G → ℂ}
    (hξ : ξ ∈ Work.CharCore.Irr G) (hres : ∀ x : H, ξ x = χ₁ x) :
    2 + (Nat.card (Submission.Blueprint.twoPoint H t) - 1) * (Nat.card Q + 1) ≤
      2 * Nat.card (Submission.Blueprint.twoPoint H t) *
        Nat.card (Submission.Blueprint.twoPoint H t) := by
  classical
  -- ## The set `L` of irreducible characters of `H` trivial on `Q`, and `L*` without `1`
  let L : Finset (H → ℂ) :=
    (Work.CharCore.Irr H).filter (fun lc => ∀ x : H, (x : G) ∈ Q → lc x = 1)
  have hLcard : L.card = Nat.card (Submission.Blueprint.twoPoint H t) :=
    final_card_lin h hz h2 hab
  have h1L : (fun _ : H => (1 : ℂ)) ∈ L := by
    rw [show L = (Work.CharCore.Irr H).filter
        (fun lc => ∀ x : H, (x : G) ∈ Q → lc x = 1) from rfl, Finset.mem_filter]
    exact ⟨Work.CharCore.principalChar_mem_Irr, fun x _ => rfl⟩
  let L' : Finset (H → ℂ) := L.erase (fun _ : H => (1 : ℂ))
  have hL'card : L'.card = Nat.card (Submission.Blueprint.twoPoint H t) - 1 := by
    show (L.erase (fun _ : H => (1 : ℂ))).card = _
    rw [Finset.card_erase_of_mem h1L, hLcard]
  -- ## Basic facts about the members of `L*`
  have hmemfacts : ∀ lc ∈ L', lc ∈ Work.CharCore.Irr H ∧
      (∀ x : H, (x : G) ∈ Q → lc x = 1) ∧ lc ≠ (fun _ : H => (1 : ℂ)) := by
    intro lc hlc
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hlc
    exact ⟨(Finset.mem_filter.mp hmem).1, (Finset.mem_filter.mp hmem).2, hne⟩
  have hne_conj : ∀ lc ∈ L', lc ≠ fun x : H => starRingEnd ℂ (lc x) := by
    intro lc hlc
    obtain ⟨hIrr, hQ, hne⟩ := hmemfacts lc hlc
    exact ne_conj_of_ne_one h hz h2 hab hIrr hQ hne
  -- ## The map `λ ↦ Ind_H^G λ`
  let F : (H → ℂ) → ↥(Work.CharCore.Irr G) := fun lc =>
    if hlc : lc ∈ L' then
      ⟨Work.Induction.indFun H lc,
        final_indFun_lin_mem_Irr_local h hz h2 hab (hmemfacts lc hlc).1 (hmemfacts lc hlc).2.1
          (hne_conj lc hlc)⟩
    else ⟨fun _ : G => (1 : ℂ), Work.CharCore.principalChar_mem_Irr⟩
  let S : Finset ↥(Work.CharCore.Irr G) := L'.image F
  have hFval : ∀ a ∈ L', (F a : G → ℂ) = Work.Induction.indFun H a := by
    intro a ha
    dsimp only [F]
    rw [dite_eq_left ha]
  -- ## The fibres of `λ ↦ Ind λ` have at most two elements
  have hfiber : ∀ b ∈ S, (L'.filter (fun a => F a = b)).card ≤ 2 := by
    intro b hb
    obtain ⟨a₀, ha₀, ha₀F⟩ := Finset.mem_image.mp hb
    obtain ⟨hIrra₀, hQa₀, -⟩ := hmemfacts a₀ ha₀
    have hIrra₀' : Work.Induction.indFun H a₀ ∈ Work.CharCore.Irr G := by
      rw [← hFval a₀ ha₀]; exact (F a₀).2
    have hsub : L'.filter (fun a => F a = b) ⊆
        ({a₀, (fun x : H => starRingEnd ℂ (a₀ x))} : Finset (H → ℂ)) := by
      intro a ha
      obtain ⟨haL', haF⟩ := Finset.mem_filter.mp ha
      obtain ⟨hIrra, hQa, _⟩ := hmemfacts a haL'
      have haF' : F a = F a₀ := by rw [haF, ha₀F]
      have hind : Work.Induction.indFun H a = Work.Induction.indFun H a₀ := by
        rw [← hFval a haL', ← hFval a₀ ha₀, congrArg Subtype.val haF']
      have hIrra' : Work.Induction.indFun H a ∈ Work.CharCore.Irr G := by
        rw [← hFval a haL']; exact (F a).2
      -- the orthogonal-character argument
      have hne0 : Work.CharCore.cfInner (Work.Induction.indFun H a₀)
          (Work.Induction.indFun H a) ≠ 0 := by
        intro hzero
        rw [hind] at hzero
        rw [Work.CharCore.irr_orthonormal _ _ hIrra₀' hIrra₀', if_pos rfl] at hzero
        exact one_ne_zero hzero
      rw [Finset.mem_insert, Finset.mem_singleton]
      by_contra hnot
      push_neg at hnot
      exact hne0 (final_linear_ne_local h hz h2 hab hIrra₀ hIrra hQa₀ hQa hnot.1 hnot.2)
    have hcard2 : ({a₀, (fun x : H => starRingEnd ℂ (a₀ x))} : Finset (H → ℂ)).card ≤ 2 := by
      calc ({a₀, (fun x : H => starRingEnd ℂ (a₀ x))} : Finset (H → ℂ)).card
          ≤ ({a₀} : Finset (H → ℂ)).card + 1 := Finset.card_insert_le _ _
        _ = 2 := by simp
    exact le_trans (Finset.card_le_card hsub) hcard2
  -- ## Hence `2 · #S ≥ d - 1`
  have hcount : Nat.card (Submission.Blueprint.twoPoint H t) - 1 ≤ 2 * S.card := by
    have hsum : L'.card = ∑ b ∈ S, (L'.filter (fun a => F a = b)).card :=
      Finset.card_eq_sum_card_fiberwise (fun a ha => Finset.mem_image.mpr ⟨a, ha, rfl⟩)
    have h1 : L'.card ≤ ∑ b ∈ S, 2 := by
      rw [hsum]
      exact Finset.sum_le_sum fun b hb => hfiber b hb
    have h2 : (∑ _b ∈ S, 2) = 2 * S.card := by
      rw [Finset.sum_const, smul_eq_mul, mul_comm]
    rw [hL'card] at h1
    rwa [h2] at h1
  -- ## `Ξ = ξ ξ̄` as a non-negative integral combination of the irreducibles
  have hΞchar : Work.CharCore.IsChar (ξ * star ξ) := isChar_mul_star hξ
  have hclassξ : Work.CharCore.IsClassFun ξ := Work.CharCore.isClassFun_of_mem_Irr hξ
  have hclassξc : Work.CharCore.IsClassFun (star ξ) := by
    rw [show star ξ = fun g => starRingEnd ℂ (ξ g) from
      funext fun g => Pi.star_apply ξ g]
    exact hclassξ.conj
  have hclassΞ : Work.CharCore.IsClassFun (ξ * star ξ) := hclassξ.mul hclassξc
  have hcoeff := (Work.CharCore.isChar_iff hclassΞ).mp hΞchar
  choose c hc using hcoeff
  let cc : ↥(Work.CharCore.Irr G) → ℕ := fun χ => c χ.1 χ.2
  have hcc : ∀ χ : ↥(Work.CharCore.Irr G),
      Work.CharCore.cfInner (ξ * star ξ) (χ : G → ℂ) = (cc χ : ℂ) := fun χ => hc χ.1 χ.2
  -- the trivial character
  let one : ↥(Work.CharCore.Irr G) :=
    ⟨fun _ : G => (1 : ℂ), Work.CharCore.principalChar_mem_Irr⟩
  have hcone : cc one = 1 := by
    have h1 : Work.CharCore.cfInner (ξ * star ξ) (fun _ : G => (1 : ℂ)) = ((1 : ℕ) : ℂ) := by
      rw [cfInner_mul_star_one hξ]; norm_num
    have h2 := hcc one
    rw [show (one : G → ℂ) = (fun _ : G => (1 : ℂ)) from rfl] at h2
    have h3 : ((cc one : ℕ) : ℂ) = ((1 : ℕ) : ℂ) := by rw [← h2, h1]
    exact Nat.cast_injective h3
  have hirrDegone : Work.CharCore.irrDeg (one : G → ℂ) = 1 := by
    have h1 := Work.CharCore.irrDeg_spec (one : ↥(Work.CharCore.Irr G)).2
    have h2 : (one : G → ℂ) 1 = (1 : ℂ) := rfl
    rw [h2] at h1
    have h3 : ((Work.CharCore.irrDeg (one : G → ℂ) : ℕ) : ℂ) = ((1 : ℕ) : ℂ) := by
      rw [← h1]; norm_num
    exact Nat.cast_injective h3
  -- ## `cc` is `1` on `S`, and every member of `S` has degree `m + 1`
  have hdegreeS : ∀ χ ∈ S, Work.CharCore.irrDeg (χ : G → ℂ) = Nat.card Q + 1 := by
    intro χ hχ
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hχ
    obtain ⟨hIrra, hQa, -⟩ := hmemfacts a ha
    rw [hFval a ha]
    have hIrra' : Work.Induction.indFun H a ∈ Work.CharCore.Irr G := by
      rw [← hFval a ha]; exact (F a).2
    have hval : (Work.Induction.indFun H a) 1 = ((Nat.card Q + 1 : ℕ) : ℂ) := by
      rw [Work.Induction.indFun_apply_one, Work.ThmG.rankOne_index h, hQa 1 Q.one_mem]
      push_cast
      ring
    have h1 := Work.CharCore.irrDeg_spec hIrra'
    rw [hval] at h1
    exact Nat.cast_injective (by simpa using h1.symm)
  have hcoeffS : ∀ χ ∈ S, cc χ = 1 := by
    intro χ hχ
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hχ
    obtain ⟨hIrra, hQa, -⟩ := hmemfacts a ha
    have hIrra' : Work.Induction.indFun H a ∈ Work.CharCore.Irr G := by
      rw [← hFval a ha]; exact (F a).2
    have h1 : Work.CharCore.cfInner (ξ * star ξ) (Work.Induction.indFun H a) = ((1 : ℕ) : ℂ) := by
      rw [cfInner_mul_star_indFun_linear h hz h2 hab hχ₁ hξ hres hQa]; norm_num
    have h2 := hcc ⟨Work.Induction.indFun H a, hIrra'⟩
    rw [h1] at h2
    have h3 : cc (F a) = cc ⟨Work.Induction.indFun H a, hIrra'⟩ := by
      rw [show F a = ⟨Work.Induction.indFun H a, hIrra'⟩ from Subtype.ext (hFval a ha)]
    rw [h3]
    exact Nat.cast_injective h2.symm
  -- ## The degree identity `d² = ∑_χ cc χ · χ(1)`
  have hΞ1 : (ξ * star ξ) 1 = ((Nat.card (Submission.Blueprint.twoPoint H t) ^ 2 : ℕ) : ℂ) := by
    have hd : χ₁ 1 = ((Nat.card (Submission.Blueprint.twoPoint H t) : ℕ) : ℂ) :=
      (excl_degree_support h hz h2 hab hχ₁).1
    have hξ1 : ξ ((1 : H) : G) = ((Nat.card (Submission.Blueprint.twoPoint H t) : ℕ) : ℂ) :=
      (hres 1).trans hd
    have hcoe : ((1 : H) : G) = (1 : G) := Subgroup.coe_one H
    simp only [Pi.mul_apply, Pi.star_apply]
    rw [← hcoe, hξ1, star_natCast]
    push_cast
    ring
  have hdeg : (Nat.card (Submission.Blueprint.twoPoint H t)) ^ 2
      = ∑ χ : ↥(Work.CharCore.Irr G),
          cc χ * Work.CharCore.irrDeg (χ : G → ℂ) := by
    have hexp := congrFun (Work.CharCore.classFun_eq_sum_irr hclassΞ) 1
    rw [hΞ1] at hexp
    have hstep : (∑ χ ∈ Work.CharCore.Irr G,
          (Work.CharCore.cfInner (ξ * star ξ) χ) • χ) 1
        = ∑ χ : ↥(Work.CharCore.Irr G),
            (cc χ : ℂ) * (Work.CharCore.irrDeg (χ : G → ℂ) : ℂ) := by
      rw [Finset.sum_apply, ← Finset.sum_coe_sort (Work.CharCore.Irr G)
        (fun χ : G → ℂ => ((Work.CharCore.cfInner (ξ * star ξ) χ) • χ) 1)]
      refine Finset.sum_congr rfl fun χ _ => ?_
      rw [Pi.smul_apply, smul_eq_mul, hcc χ, Work.CharCore.irrDeg_spec χ.2]
    rw [hstep] at hexp
    have hcast : ((∑ χ : ↥(Work.CharCore.Irr G),
          cc χ * Work.CharCore.irrDeg (χ : G → ℂ) : ℕ) : ℂ)
        = ∑ χ : ↥(Work.CharCore.Irr G),
            (cc χ : ℂ) * (Work.CharCore.irrDeg (χ : G → ℂ) : ℂ) := by
      rw [Nat.cast_sum]
      exact Finset.sum_congr rfl fun χ _ => by rw [Nat.cast_mul]
    rw [← hcast] at hexp
    exact Nat.cast_injective hexp
  -- ## `#S · (m+1) ≤ d² - 1`
  have hmain : S.card * (Nat.card Q + 1)
      ≤ (Nat.card (Submission.Blueprint.twoPoint H t)) ^ 2 - 1 := by
    have hone : one ∉ S := by
      intro hone'
      have h1 := hdegreeS one hone'
      rw [hirrDegone] at h1
      have h2 : 2 ≤ Nat.card Q + 1 := by
        have := Nat.card_pos (α := ↥Q)
        omega
      omega
    have hsub : S ⊆ Finset.univ.erase one := by
      intro χ hχ
      rw [Finset.mem_erase]
      exact ⟨fun hEq => hone (hEq ▸ hχ), Finset.mem_univ χ⟩
    have hsplit := Finset.sum_erase_add (Finset.univ : Finset ↥(Work.CharCore.Irr G))
      (fun χ => cc χ * Work.CharCore.irrDeg (χ : G → ℂ)) (Finset.mem_univ one)
    have hsplit' : (∑ χ ∈ Finset.univ.erase one, cc χ * Work.CharCore.irrDeg (χ : G → ℂ))
        = (Nat.card (Submission.Blueprint.twoPoint H t)) ^ 2 - 1 := by
      have h1 : cc one * Work.CharCore.irrDeg (one : G → ℂ) = 1 := by
        rw [hcone, hirrDegone, mul_one]
      rw [h1, ← hdeg] at hsplit
      omega
    have hle : ∑ χ ∈ S, cc χ * Work.CharCore.irrDeg (χ : G → ℂ)
        ≤ ∑ χ ∈ Finset.univ.erase one, cc χ * Work.CharCore.irrDeg (χ : G → ℂ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun χ _ _ => Nat.zero_le _)
    have hSeval : S.card * (Nat.card Q + 1)
        = ∑ χ ∈ S, cc χ * Work.CharCore.irrDeg (χ : G → ℂ) := by
      rw [Finset.sum_congr rfl fun χ hχ => by rw [hcoeffS χ hχ, one_mul, hdegreeS χ hχ]]
      simp [Finset.sum_const, smul_eq_mul, mul_comm]
    rw [hSeval]
    exact le_trans hle (le_of_eq hsplit')
  -- ## The final arithmetic
  have hle : (Nat.card (Submission.Blueprint.twoPoint H t) - 1) * (Nat.card Q + 1)
      ≤ 2 * ((Nat.card (Submission.Blueprint.twoPoint H t)) ^ 2 - 1) := by
    have h1 : (Nat.card (Submission.Blueprint.twoPoint H t) - 1) * (Nat.card Q + 1)
        ≤ (2 * S.card) * (Nat.card Q + 1) := Nat.mul_le_mul_right _ hcount
    have h2 : (2 * S.card) * (Nat.card Q + 1) = 2 * (S.card * (Nat.card Q + 1)) := by ring
    have h3 : 2 * (S.card * (Nat.card Q + 1))
        ≤ 2 * ((Nat.card (Submission.Blueprint.twoPoint H t)) ^ 2 - 1) :=
      Nat.mul_le_mul_left 2 hmain
    exact le_trans h1 (le_trans (le_of_eq h2) h3)
  calc 2 + (Nat.card (Submission.Blueprint.twoPoint H t) - 1) * (Nat.card Q + 1)
      ≤ 2 + 2 * ((Nat.card (Submission.Blueprint.twoPoint H t)) ^ 2 - 1) :=
        Nat.add_le_add_left hle 2
    _ = 2 * Nat.card (Submission.Blueprint.twoPoint H t) *
          Nat.card (Submission.Blueprint.twoPoint H t) := by
        have hD2 : 1 ≤ Nat.card (Submission.Blueprint.twoPoint H t) *
            Nat.card (Submission.Blueprint.twoPoint H t) :=
          Nat.mul_pos (Nat.card_pos) (Nat.card_pos)
        rw [pow_two, Nat.mul_sub_left_distrib, Nat.mul_one, mul_assoc]
        omega

end Work.ZassenhausPSL2.Feit
