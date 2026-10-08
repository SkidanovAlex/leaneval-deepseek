import Mathlib
import Submission.Work.CharPrelim.Defs
import Submission.Work.CharPrelim.clifford_res_eq_smul_of_invariant

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.CharPrelim

/-! ### Auxiliary facts for `indFun_eq_smul_sum_image`

These are the small computational ingredients of the Clifford count for a commutative
quotient.  Everything is stated in the vocabulary of `Work.CharCore` / `Work.Clifford` /
`Work.Induction`. -/

/-- In a commutative quotient every irreducible character has degree one, so it takes the
value `1` at `1`. -/
theorem one_apply_of_mem_Irr_of_commutative {H : Type*} [Group H] [Fintype H]
    [IsMulCommutative H] {β : H → ℂ} (hβ : β ∈ Work.CharCore.Irr H) : β 1 = 1 := by
  rw [Work.CharCore.irrDeg_spec hβ, Work.CharCore.irrDeg_eq_one_of_commutative hβ]
  norm_num

/-- The regular-character identity for the irreducible characters of a commutative group, at
the identity: `∑_{β ∈ Irr H} β 1 = |H|`. -/
theorem sum_irr_apply_one_of_commutative {H : Type*} [Group H] [Fintype H]
    [IsMulCommutative H] :
    ∑ β ∈ Work.CharCore.Irr H, β (1 : H) = (Nat.card H : ℂ) := by
  rw [show (∑ β ∈ Work.CharCore.Irr H, β (1 : H))
      = ∑ β ∈ Work.CharCore.Irr H, β 1 * β 1 from
    Finset.sum_congr rfl fun β hβ => by rw [one_apply_of_mem_Irr_of_commutative hβ]; ring]
  rw [Work.Clifford.sum_irr_deg_mul_apply (H := H) 1, if_pos rfl]

/-- The regular-character identity for the irreducible characters of a commutative group, off
the identity: `∑_{β ∈ Irr H} β h = 0` for `h ≠ 1`. -/
theorem sum_irr_apply_ne_one_of_commutative {H : Type*} [Group H] [Fintype H]
    [IsMulCommutative H] {h : H} (hh : h ≠ 1) :
    ∑ β ∈ Work.CharCore.Irr H, β h = 0 := by
  rw [show (∑ β ∈ Work.CharCore.Irr H, β h)
      = ∑ β ∈ Work.CharCore.Irr H, β 1 * β h from
    Finset.sum_congr rfl fun β hβ => by rw [one_apply_of_mem_Irr_of_commutative hβ, one_mul]]
  rw [Work.Clifford.sum_irr_deg_mul_apply (H := H) h, if_neg hh]

/-- Multiplying by the inflation of a character of the quotient does not change the
restriction to `N` (the inflation of a linear character is trivial on `N`). -/
theorem resFun_mul_inflateFun_eq {G : Type*} [Group G] [Fintype G] {N : Subgroup G} [N.Normal]
    [Fintype ↥N] [Fintype (G ⧸ N)] [IsMulCommutative (G ⧸ N)] {β : G ⧸ N → ℂ}
    (hβ : β ∈ Work.CharCore.Irr (G ⧸ N)) (lam : G → ℂ) :
    Work.Clifford.resFun N (lam * Work.Clifford.inflateFun N β)
      = Work.Clifford.resFun N lam := by
  funext n
  show lam (n : G) * Work.Clifford.inflateFun N β (n : G) = lam (n : G)
  have h1 : Work.Clifford.inflateFun N β (n : G) = β 1 := by
    show β (QuotientGroup.mk (n : G)) = β 1
    rw [show (QuotientGroup.mk (n : G) : G ⧸ N) = 1 from
      (QuotientGroup.eq_one_iff (n : G)).mpr n.2]
  rw [h1, one_apply_of_mem_Irr_of_commutative hβ, mul_one]

/-- Gallagher's theorem, `Irr`-side, for a commutative quotient: for `N ⊴ G` with `G ⧸ N`
commutative, `β ∈ Irr (G ⧸ N)` and `lam ∈ Irr G`, the product `lam · inflateFun N β` is
irreducible, of the same degree as `lam`. -/
theorem mul_inflateFun_mem_Irr_of_commutative {G : Type*} [Group G] [Fintype G]
    {N : Subgroup G} [N.Normal] [Fintype ↥N] [Fintype (G ⧸ N)] [IsMulCommutative (G ⧸ N)]
    {lam : G → ℂ} (hlam : lam ∈ Work.CharCore.Irr G) {β : G ⧸ N → ℂ}
    (hβ : β ∈ Work.CharCore.Irr (G ⧸ N)) :
    lam * Work.Clifford.inflateFun N β ∈ Work.CharCore.Irr G ∧
      Work.CharCore.irrDeg (lam * Work.Clifford.inflateFun N β)
        = Work.CharCore.irrDeg lam := by
  classical
  have hβ1 : β 1 = 1 := one_apply_of_mem_Irr_of_commutative hβ
  -- `β` is a linear character, so it is multiplicative
  obtain ⟨φ, hφ⟩ := (Work.CharCore.linear_char_iff_deg_one hβ).mp
    (Work.CharCore.irrDeg_eq_one_of_commutative hβ)
  have hmul : ∀ y z : G ⧸ N, β (y * z) = β y * β z := by
    intro y z
    rw [hφ (y * z), map_mul, Units.val_mul, ← hφ y, ← hφ z]
  have hunit : ∀ y : G ⧸ N, β y * starRingEnd ℂ (β y) = 1 := by
    intro y
    rw [Work.CharCore.star_Irr β hβ y, ← hmul y y⁻¹, mul_inv_cancel, hβ1]
  have hpt : ∀ x : G,
      (lam * Work.Clifford.inflateFun N β) x
          * starRingEnd ℂ ((lam * Work.Clifford.inflateFun N β) x)
        = lam x * starRingEnd ℂ (lam x) := by
    intro x
    show (lam x * β (QuotientGroup.mk x)) * starRingEnd ℂ (lam x * β (QuotientGroup.mk x))
      = lam x * starRingEnd ℂ (lam x)
    rw [map_mul, mul_mul_mul_comm, hunit (QuotientGroup.mk x), mul_one]
  -- the norm of the product is `⟪lam, lam⟫ = 1`
  have hnorm : Work.CharCore.cfInner (lam * Work.Clifford.inflateFun N β)
      (lam * Work.Clifford.inflateFun N β) = 1 := by
    have hsum : (∑ x : G, (lam * Work.Clifford.inflateFun N β) x
        * starRingEnd ℂ ((lam * Work.Clifford.inflateFun N β) x))
        = ∑ x : G, lam x * starRingEnd ℂ (lam x) := Finset.sum_congr rfl fun x _ => hpt x
    have h1 : Work.CharCore.cfInner lam lam = 1 := by
      rw [Work.CharCore.irr_orthonormal lam lam hlam hlam]
      simp
    rw [Work.CharCore.cfInner_apply, hsum, ← Work.CharCore.cfInner_apply]
    exact h1
  -- it is a virtual character
  have hV : Work.CharCore.IsVChar (lam * Work.Clifford.inflateFun N β) :=
    Work.CharCore.isVChar_mul_of_mem_Irr_left hlam
      (Work.CharCore.IsChar.toVChar
        (Work.Clifford.isChar_inflateFun (Work.Clifford.charCore_mem_Irr_subset β hβ)))
  obtain ⟨ψ, hψ, hcase⟩ := Work.CharCore.vchar_norm_one hV hnorm
  have hf1 : (lam * Work.Clifford.inflateFun N β) 1 = (Work.CharCore.irrDeg lam : ℂ) := by
    show lam (1 : G) * β 1 = (Work.CharCore.irrDeg lam : ℂ)
    rw [hβ1, mul_one, Work.CharCore.irrDeg_spec hlam]
  have hmem : lam * Work.Clifford.inflateFun N β ∈ Work.CharCore.Irr G := by
    rcases hcase with h | h
    · rw [h]; exact hψ
    · exfalso
      have hcast : (Work.CharCore.irrDeg lam : ℝ) = -(Work.CharCore.irrDeg ψ : ℝ) := by
        have h2 : (Work.CharCore.irrDeg lam : ℂ) = -(Work.CharCore.irrDeg ψ : ℂ) := by
          rw [← hf1, h, Pi.neg_apply, Work.CharCore.irrDeg_spec hψ]
        have := congrArg Complex.re h2
        simpa using this
      have hpos1 : (0 : ℝ) < (Work.CharCore.irrDeg lam : ℝ) :=
        Work.CharCore.irrDeg_pos' hlam
      have hpos2 : (0 : ℝ) < (Work.CharCore.irrDeg ψ : ℝ) := Work.CharCore.irrDeg_pos' hψ
      linarith
  exact ⟨hmem, Nat.cast_injective (by
    rw [← Work.CharCore.irrDeg_spec hmem, hf1])⟩

/-- The value of an induced function at an element of the subgroup, for an invariant
function: `Ind_N^G θ n = [G : N] · θ n` for `n ∈ N`. -/
theorem indFun_apply_of_mem_of_invariant {G : Type*} [Group G] [Fintype G] {N : Subgroup G}
    [N.Normal] [Fintype ↥N] {θ : ↥N → ℂ} (hinv : Work.Clifford.inertia N θ = ⊤) (n : ↥N) :
    Work.Induction.indFun N θ n = (N.index : ℂ) * θ n := by
  classical
  have hconj : ∀ x : G, x * (n : G) * x⁻¹ ∈ N :=
    fun x => (inferInstance : N.Normal).conj_mem (n : G) n.2 x
  have hval : ∀ x : G, θ ⟨x * (n : G) * x⁻¹, hconj x⟩ = θ n := by
    intro x
    have hx := (Work.Clifford.mem_inertia N θ x).mp (by rw [hinv]; exact Subgroup.mem_top x)
    have h2 := congrFun hx n
    rwa [Work.Clifford.conjFun_apply] at h2
  have hterm : ∀ x : G,
      (if hx : x * (n : G) * x⁻¹ ∈ N then θ ⟨x * (n : G) * x⁻¹, hx⟩ else 0) = θ n := by
    intro x
    rw [dif_pos (hconj x)]
    exact hval x
  have hcard : (Nat.card ↥N : ℂ) * (N.index : ℂ) = (Nat.card G : ℂ) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, Subgroup.index_eq_card, Nat.cast_mul]
    ring
  have hN : (Nat.card ↥N : ℂ) ≠ 0 := by
    simp [Nat.card_eq_fintype_card]
  rw [Work.Induction.indFun_apply_def, Finset.sum_congr rfl fun x _ => hterm x,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card (α := G),
    ← hcard]
  rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hN, one_mul]

/-- The pointwise identity behind Gallagher's formula: the sum of the products
`lam · inflateFun N β` over `β ∈ Irr (G ⧸ N)` equals `e • Ind_N^G θ` when `lam|_N = e • θ`,
`θ` is `G`-invariant and `G ⧸ N` is commutative. -/
theorem sum_mul_inflateFun_eq_smul_indFun {G : Type*} [Group G] [Fintype G] {N : Subgroup G}
    [N.Normal] [Fintype ↥N] [Fintype (G ⧸ N)] [IsMulCommutative (G ⧸ N)]
    {θ : ↥N → ℂ} (hinv : Work.Clifford.inertia N θ = ⊤) {lam : G → ℂ} {e : ℕ}
    (hres : Work.Induction.resFun N lam = (e : ℂ) • θ) :
    (∑ β ∈ Work.CharCore.Irr (G ⧸ N), lam * Work.Clifford.inflateFun N β)
      = (e : ℂ) • Work.Induction.indFun N θ := by
  classical
  funext x
  rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hLHS : (∑ β ∈ Work.CharCore.Irr (G ⧸ N),
      (lam * Work.Clifford.inflateFun N β) x)
      = lam x * (∑ β ∈ Work.CharCore.Irr (G ⧸ N), β (QuotientGroup.mk x)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun β _ => by
      simp only [Pi.mul_apply, Work.Clifford.inflateFun]
  rw [hLHS]
  by_cases hx : x ∈ N
  · have hmk : (QuotientGroup.mk x : G ⧸ N) = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    have hlx : lam x = (e : ℂ) * θ ⟨x, hx⟩ := by
      have h := congrFun hres ⟨x, hx⟩
      simpa [Work.Induction.resFun_apply, Pi.smul_apply] using h
    rw [hmk, sum_irr_apply_one_of_commutative (H := G ⧸ N),
      indFun_apply_of_mem_of_invariant hinv ⟨x, hx⟩,
      show (Nat.card (G ⧸ N) : ℂ) = (N.index : ℂ) from by rw [Subgroup.index_eq_card],
      hlx]
    ring
  · have hconj : ∀ y : G, y * x * y⁻¹ ∉ N := by
      intro y hy
      exact hx (by
        have h := (inferInstance : N.Normal).conj_mem (y * x * y⁻¹) hy y⁻¹
        rwa [show y⁻¹ * (y * x * y⁻¹) * (y⁻¹)⁻¹ = x from by group] at h)
    have hne : (QuotientGroup.mk x : G ⧸ N) ≠ 1 :=
      fun h => hx ((QuotientGroup.eq_one_iff x).mp h)
    rw [sum_irr_apply_ne_one_of_commutative (H := G ⧸ N) hne, mul_zero,
      Work.Induction.indFun_apply_eq_zero N θ x hconj, mul_zero]

/-- The Clifford count for a commutative quotient: for `θ ∈ Irr N` invariant under the finite
group `G` with `N ⊴ G` and `G ⧸ N` commutative, and `lam ∈ Irr G` lying over `θ`, one has
`res_N lam = e • θ` for a positive natural `e`, every product `lam * infl β` (`β ∈ Irr (G ⧸ N)`)
is irreducible of the same degree, and `Ind_N^G θ = e • ∑_{χ ∈ image} χ` (sum over distinct
values).

Suggested route.  (i) `Work.Clifford.clifford_decomposition` applied to `lam` writes
`res_N lam = e • orbitSum N θ'`; `hinv` forces every conjugate of `θ` to be `θ`, so
`charOrbit N θ = {θ}` and `orbitSum N θ = θ`; the hypothesis `hlamθ` shows `θ` is in the orbit of
`θ'`, hence `θ'` has the same orbit as `θ`; this gives `res_N lam = e • θ`, `e > 0`.
(ii) `β ∈ Irr (G ⧸ N)` with `G ⧸ N` commutative has `β 1 = 1` (`irrDeg_eq_one_of_commutative`
plus `linear_char_iff_deg_one`), so `inflateFun N β` is a linear character; `lam * inflateFun N β`
is a virtual character (`isVChar_mul_of_mem_Irr_left` with `Work.Clifford.isChar_inflateFun`),
its norm is `1` (the linear factor has values of modulus `1`), so
`Work.CharCore.vchar_norm_one` and positivity of the degree give irreducibility, and its degree is
`irrDeg lam` because `β 1 = 1`.
(iii) Evaluate both sides of the desired identity at `x : G` after expanding the left hand side as
`∑_{β} lam x * inflateFun N β x = lam x * ∑_{β} β 1 * β (x N)`: at `x ∈ N` use
`∑_{β} β 1 = N.index` (from `Work.CharCore.sum_irr_degree_sq` on `G ⧸ N` and `β 1 = 1`, with
`Subgroup.index_eq_card`), at `x ∉ N` use that both sides vanish
(`Work.Clifford.sum_irr_deg_mul_apply` and `Work.Induction.indFun_apply_eq_zero` + normality);
combine with `res_N lam = e • θ`.
(iv) The pointwise identity says `∑_{β} lam * inflateFun N β = e • Ind_N^G θ`; taking inner
products with `χ ∈ Irr G` (`Work.CharCore.irr_orthonormal`) and using Frobenius reciprocity plus
`res_N χ = e • θ` for `χ` in the image shows the multiplicities are `e` on the image and `0`
outside it; `Work.CharCore.classFun_eq_sum_irr` together with
`Work.CharCore.isClassFun_of_mem_Irr`-style facts for `Ind_N^G θ` then gives the claim. -/
theorem indFun_eq_smul_sum_image {G : Type*} [Group G] [Fintype G] {N : Subgroup G} [N.Normal]
    [Fintype ↥N] [Fintype (G ⧸ N)] {θ : ↥N → ℂ} (hθ : θ ∈ Work.CharCore.Irr ↥N)
    (hinv : Work.Clifford.inertia N θ = ⊤) [IsMulCommutative (G ⧸ N)]
    {lam : G → ℂ} (hlam : lam ∈ Work.CharCore.Irr G)
    (hlamθ : Work.CharCore.cfInner θ (Work.Induction.resFun N lam) ≠ 0) :
    ∃ e : ℕ, 0 < e ∧
      Work.Induction.resFun N lam = (e : ℂ) • θ ∧
      (∀ β ∈ Work.CharCore.Irr (G ⧸ N),
        lam * Work.Clifford.inflateFun N β ∈ Work.CharCore.Irr G ∧
          Work.CharCore.irrDeg (lam * Work.Clifford.inflateFun N β) = Work.CharCore.irrDeg lam) ∧
      Work.Induction.indFun N θ =
        (e : ℂ) • ∑ χ ∈ (Work.CharCore.Irr (G ⧸ N)).image
            (fun β => lam * Work.Clifford.inflateFun N β), χ := by
  classical
  obtain ⟨e, he, hres⟩ := clifford_res_eq_smul_of_invariant hθ hinv hlam hlamθ
  refine ⟨e, he, hres, fun β hβ => mul_inflateFun_mem_Irr_of_commutative hlam hβ, ?_⟩
  set img : Finset (G → ℂ) :=
    (Work.CharCore.Irr (G ⧸ N)).image (fun β => lam * Work.Clifford.inflateFun N β) with himg
  -- the pointwise identity of Gallagher's formula
  have hL := sum_mul_inflateFun_eq_smul_indFun (N := N) hinv hres
  have hirr_img : ∀ χ ∈ img, χ ∈ Work.CharCore.Irr G := by
    intro χ hχ
    obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.mp hχ
    exact (mul_inflateFun_mem_Irr_of_commutative hlam hβ).1
  -- the equality of inner products with every irreducible character
  have hcases : ∀ ψ ∈ Work.CharCore.Irr G,
      Work.CharCore.cfInner (Work.Induction.indFun N θ) ψ
        = Work.CharCore.cfInner ((e : ℂ) • ∑ χ ∈ img, χ) ψ := by
    intro ψ hψ
    show Work.Clifford.cfInner (Work.Clifford.indFun N θ) ψ
        = Work.Clifford.cfInner ((e : ℂ) • ∑ χ ∈ img, χ) ψ
    have hψC : ψ ∈ Work.Clifford.Irr G := Work.Clifford.charCore_mem_Irr_subset ψ hψ
    rw [Work.Clifford.cfInner_indFun θ (Work.Clifford.IsClassFun.of_mem_Irr hψC),
      Work.Clifford.cfInner_smul_left, Work.Clifford.cfInner_sum_left]
    have hsum : (∑ χ ∈ img, Work.Clifford.cfInner χ ψ)
        = ∑ χ ∈ img, (if χ = ψ then (1 : ℂ) else 0) := by
      refine Finset.sum_congr rfl fun χ hχ => ?_
      obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.mp hχ
      exact Work.Clifford.cfInner_eq_ite_of_mem_Irr
        (Work.Clifford.charCore_mem_Irr_subset _
          (mul_inflateFun_mem_Irr_of_commutative hlam hβ).1) hψC
    rw [hsum, Finset.sum_ite_eq' img ψ (fun _ => (1 : ℂ))]
    by_cases hψimg : ψ ∈ img
    · rw [if_pos hψimg, mul_one]
      obtain ⟨β, hβ, hβψ⟩ := Finset.mem_image.mp hψimg
      have hθC : θ ∈ Work.Clifford.Irr ↥N := (Work.Clifford.mem_Irr_charCore_iff).mpr hθ
      have hresψ : Work.Clifford.resFun N ψ = (e : ℂ) • θ := by
        rw [← hβψ]
        funext n
        show lam (n : G) * Work.Clifford.inflateFun N β (n : G) = ((e : ℂ) • θ) n
        have h1 : Work.Clifford.inflateFun N β (n : G) = β 1 := by
          show β (QuotientGroup.mk (n : G)) = β 1
          rw [show (QuotientGroup.mk (n : G) : G ⧸ N) = 1 from
            (QuotientGroup.eq_one_iff (n : G)).mpr n.2]
        rw [h1, one_apply_of_mem_Irr_of_commutative hβ, mul_one]
        simpa using congrFun hres n
      rw [hresψ, Work.Clifford.cfInner_smul_right,
        Work.Clifford.cfInner_eq_ite_of_mem_Irr hθC hθC]
      simp
    · rw [if_neg hψimg, mul_zero]
      -- the coefficients of `Ind_N^G θ` outside the image vanish
      have h1 : Work.Clifford.cfInner (∑ β ∈ Work.CharCore.Irr (G ⧸ N),
          lam * Work.Clifford.inflateFun N β) ψ = 0 := by
        rw [Work.Clifford.cfInner_sum_left]
        refine Finset.sum_eq_zero fun β hβ => ?_
        rw [Work.Clifford.cfInner_eq_ite_of_mem_Irr
          (Work.Clifford.charCore_mem_Irr_subset _
            (mul_inflateFun_mem_Irr_of_commutative hlam hβ).1) hψC, if_neg]
        intro hβψ
        exact hψimg (Finset.mem_image.mpr ⟨β, hβ, hβψ⟩)
      rw [hL] at h1
      rw [Work.Clifford.cfInner_smul_left] at h1
      have he0 : (e : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr he.ne'
      have h2 : Work.Clifford.cfInner (Work.Clifford.indFun N θ) ψ = 0 :=
        (mul_eq_zero.mp h1).resolve_left he0
      rw [Work.Clifford.cfInner_indFun θ (Work.Clifford.IsClassFun.of_mem_Irr hψC)] at h2
      exact h2
  have hclassf : Work.CharCore.IsClassFun (Work.Induction.indFun N θ) :=
    Work.Induction.isClassFun_indFun N θ
  have hclassg : Work.CharCore.IsClassFun (∑ χ ∈ img, χ) :=
    Work.CharCore.IsClassFun.sum img (fun χ => χ) fun χ hχ =>
      Work.CharCore.isClassFun_of_mem_Irr (hirr_img χ hχ)
  have hzero : Work.Induction.indFun N θ - (e : ℂ) • ∑ χ ∈ img, χ = 0 :=
    Work.CharCore.classFun_eq_zero_of_orthogonal
      (Work.CharCore.IsClassFun.sub hclassf (Work.CharCore.IsClassFun.smul _ hclassg))
      (fun ψ hψ => by rw [Work.CharCore.cfInner_sub_left, hcases ψ hψ, sub_self])
  exact sub_eq_zero.mp hzero

end Work.CharPrelim
