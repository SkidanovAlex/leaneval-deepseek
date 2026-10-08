import Mathlib
import Submission.Work.PGroup.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# A finite symplectic space over `ZMod p` has cardinality `p ^ (2 * n)`

If `V` is a finite module over the prime field `ZMod p` carrying a non-degenerate
alternating bilinear form `B`, then `V` is even dimensional, so its cardinality is
an even power of `p`.

The mathematical content is the classical fact that a non-degenerate alternating
(equivalently symplectic) form exists on a finite dimensional vector space only in
even dimension.  The proof here runs by strong induction on the dimension: given a
nonzero vector `x` there is `w` with `B x w ≠ 0`; the plane `W = span {x, w}` is a
non-degenerate subspace (its Gram matrix is `[[0, c], [-c, 0]]` with `c ≠ 0`), hence
`V = W ⊥ Wᵀ` with `Wᵀ = B.orthogonal W`, and `B` restricted to `Wᵀ` is again a
non-degenerate alternating form on a space of dimension `dim V - 2`.  Induction gives
evenness of the dimension.
-/

set_option linter.style.haveILetI false

noncomputable section

namespace Work.PGroup.Symplectic

universe u v

/-- For an alternating form `B` and vectors `x`, `w` with `B x w ≠ 0`, the plane
`span {x, w}` is disjoint from its orthogonal complement. -/
private theorem disjoint_span_pair_orthogonal {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {B : LinearMap.BilinForm K V} (hB : B.IsAlt) {x w : V} (hxw : B x w ≠ 0) :
    Disjoint (Submodule.span K ({x, w} : Set V))
      (B.orthogonal (Submodule.span K ({x, w} : Set V))) := by
  rw [Submodule.disjoint_def]
  intro m hm hmorth
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hm
  have hxmem : x ∈ Submodule.span K ({x, w} : Set V) := Submodule.subset_span (by simp)
  have hwmem : w ∈ Submodule.span K ({x, w} : Set V) := Submodule.subset_span (by simp)
  have h1 : b * B x w = 0 := by
    have h := hmorth x hxmem
    rw [map_add, map_smul, map_smul, hB.self_eq_zero x, smul_zero, zero_add, smul_eq_mul] at h
    exact h
  have h2 : a * B w x = 0 := by
    have h := hmorth w hwmem
    rw [map_add, map_smul, map_smul, hB.self_eq_zero w, smul_zero, add_zero, smul_eq_mul] at h
    exact h
  have hb : b = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact h
    · exact absurd h hxw
  have hwx : B w x ≠ 0 := by
    rw [← hB.neg_eq x w]
    exact neg_ne_zero.mpr hxw
  have ha : a = 0 := by
    rcases mul_eq_zero.mp h2 with h | h
    · exact h
    · exact absurd h hwx
  rw [ha, hb, zero_smul, zero_smul, add_zero]

/-- For an alternating form `B` and vectors `x`, `w` with `B x w ≠ 0`, the plane
`span {x, w}` has dimension `2`. -/
private theorem finrank_span_pair_eq_two {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {B : LinearMap.BilinForm K V} (hB : B.IsAlt) {x w : V} (hxw : B x w ≠ 0) :
    Module.finrank K (Submodule.span K ({x, w} : Set V)) = 2 := by
  have hwx : B w x ≠ 0 := by
    rw [← hB.neg_eq x w]
    exact neg_ne_zero.mpr hxw
  have hli : LinearIndependent K ![x, w] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht : t = 0 := by
      have h := congrArg (B x) hst
      simp only [map_add, map_smul, hB.self_eq_zero x, smul_eq_mul, mul_zero, zero_add,
        map_zero] at h
      rcases mul_eq_zero.mp h with h | h
      · exact h
      · exact absurd h hxw
    have hs : s = 0 := by
      have h := congrArg (B w) hst
      rw [ht, zero_smul, add_zero] at h
      simp only [map_smul, smul_eq_mul, map_zero] at h
      rcases mul_eq_zero.mp h with h | h
      · exact h
      · exact absurd h hwx
    exact ⟨hs, ht⟩
  have hrange : Set.range ![x, w] = ({x, w} : Set V) := by
    ext y; constructor
    · rintro ⟨i, rfl⟩; fin_cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  rw [← hrange]
  simpa using finrank_span_eq_card (R := K) (M := V) hli

/-- Over a field, a non-degenerate alternating form forces the (finite) dimension to be even.
Strong induction on the dimension, splitting off a hyperbolic plane. -/
private theorem even_finrank_aux {K : Type u} [Field K] (d : ℕ) :
    ∀ (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (B : LinearMap.BilinForm K V), Module.finrank K V = d →
      B.IsAlt → B.Nondegenerate → Even d := by
  refine Nat.strong_induction_on d ?_
  intro d ih V _ _ _ B hfin halt hnd
  rcases eq_or_ne d 0 with hd0 | hd0
  · rw [hd0]; exact Even.zero
  · haveI : Nontrivial V :=
      Module.finrank_pos_iff.mp (by rw [hfin]; exact Nat.pos_of_ne_zero hd0)
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    obtain ⟨w, hw⟩ : ∃ w, B x w ≠ 0 := by
      by_contra hcon
      rw [not_exists] at hcon
      simp only [not_not] at hcon
      exact hx (hnd.1 x hcon)
    set W : Submodule K V := Submodule.span K ({x, w} : Set V) with hWdef
    have hdisj : Disjoint W (B.orthogonal W) := by
      rw [hWdef]
      exact disjoint_span_pair_orthogonal halt hw
    have hcompl : IsCompl W (B.orthogonal W) :=
      (LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint (B := B) (W := W) halt.isRefl).mpr hdisj
    have hfinW : Module.finrank K W = 2 := by
      rw [hWdef]
      exact finrank_span_pair_eq_two halt hw
    have hsum : Module.finrank K V = Module.finrank K W + Module.finrank K (B.orthogonal W) := by
      have h := Submodule.finrank_sup_add_finrank_inf_eq (K := K) W (B.orthogonal W)
      rw [hcompl.sup_eq_top, hcompl.inf_eq_bot, finrank_top, finrank_bot] at h
      simpa using h
    have hUalt : (B.restrict (B.orthogonal W)).IsAlt := fun u => halt (u : V)
    have hUnd : (B.restrict (B.orthogonal W)).Nondegenerate := by
      rw [LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal (B := B) halt.isRefl,
          LinearMap.BilinForm.orthogonal_orthogonal (B := B) hnd halt.isRefl W]
      exact hcompl.symm
    have hd_eq : d = 2 + Module.finrank K (B.orthogonal W) := by
      rw [← hfin, hsum, hfinW]
    have hU_lt : Module.finrank K (B.orthogonal W) < d := by
      rw [hd_eq]; omega
    have hEvenU : Even (Module.finrank K (B.orthogonal W)) :=
      ih (Module.finrank K (B.orthogonal W)) hU_lt (B.orthogonal W)
        (B.restrict (B.orthogonal W)) rfl hUalt hUnd
    rw [hd_eq]
    exact even_two.add hEvenU

/-- Over a field, a non-degenerate alternating form on a finite dimensional space forces
the dimension to be even. -/
private theorem even_finrank_of_nondegenerate_alt {K : Type u} [Field K]
    (V : Type v) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (B : LinearMap.BilinForm K V) (halt : B.IsAlt) (hnd : B.Nondegenerate) :
    Even (Module.finrank K V) :=
  even_finrank_aux (K := K) (Module.finrank K V) V B rfl halt hnd

/-- A finite module over the prime field `ZMod p` carrying a non-degenerate alternating
bilinear form has cardinality an even power of `p`. -/
theorem card_eq_pow_even_of_nondegenerate_alt {p : ℕ} (hp : p.Prime)
    (V : Type*) [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod p) V) (halt : B.IsAlt) (hnd : B.Nondegenerate) :
    ∃ n : ℕ, Nat.card V = p ^ (2 * n) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  obtain ⟨n, hn⟩ := even_finrank_of_nondegenerate_alt (K := ZMod p) V B halt hnd
  refine ⟨n, ?_⟩
  rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod, hn, two_mul]

end Work.PGroup.Symplectic
