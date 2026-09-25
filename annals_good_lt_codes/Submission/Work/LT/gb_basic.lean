import Mathlib
import Submission.Work.LT.good_base_defs
import Submission.Work.LT.gb_prodSum_pairCond

/-!
# Elementary helpers for the good base code proof

Small, self-contained lemmas used by the counting and assembling parts of
`Work.LT.good_base_code`: powers of `2` with real exponents, cardinalities of `𝔽₂`-vector spaces,
the distance consequence of Kalachev--Panteleev property `(*)`, and the trivial bounds on the
number of non-zero rows/columns of a matrix.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Work.LT

open GB

lemma rpow_two_mul (a b : ℝ) : (2:ℝ)^a * (2:ℝ)^b = (2:ℝ)^(a+b) :=
  (Real.rpow_add (by norm_num) a b).symm

lemma rpow_two_sub (a b : ℝ) : (2:ℝ)^(a - b) = (2:ℝ)^a / (2:ℝ)^b :=
  Real.rpow_sub (by norm_num) a b

lemma rpow_two_le_iff {a b : ℝ} : (2:ℝ)^a ≤ (2:ℝ)^b ↔ a ≤ b :=
  Real.rpow_le_rpow_left_iff (by norm_num)

lemma rpow_two_lt_iff {a b : ℝ} : (2:ℝ)^a < (2:ℝ)^b ↔ a < b :=
  Real.rpow_lt_rpow_left_iff (by norm_num)

lemma rpow_two_natCast (n : ℕ) : (2:ℝ)^n = (2:ℝ)^(n:ℝ) := (Real.rpow_natCast 2 n).symm

lemma rpow_two_mul_nat (r D : ℕ) : (2:ℝ)^(r*D) = (2:ℝ)^((r:ℝ)*D) := by
  rw [rpow_two_natCast]
  congr 1
  push_cast
  ring

lemma rpow_two_mul_nat_two (r D : ℕ) : (2:ℝ)^(2*r*D) = (2:ℝ)^(2*(r:ℝ)*D) := by
  rw [rpow_two_natCast]
  congr 1
  push_cast
  ring

lemma cast_two_pow_mul (r D : ℕ) : (((2:ℕ)^(D*r) : ℕ) : ℝ) = (2:ℝ)^((r:ℝ)*D) := by
  rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
  congr 1
  push_cast
  ring

lemma card_filter_eq_natCard {ι : Type*} [Fintype ι] (p : ι → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card = Nat.card {x // p x} := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

lemma card_fun_zmod_cast (r D : ℕ) :
    (Fintype.card (Fin r → Fin D → ZMod 2) : ℝ) = (2:ℝ)^((r:ℝ)*D) := by
  have hnat : Fintype.card (Fin r → Fin D → ZMod 2) = 2^(D*r) := by
    rw [Fintype.card_fun, Fintype.card_fun, ZMod.card, Fintype.card_fin, Fintype.card_fin,
      ← pow_mul]
  rw [hnat, cast_two_pow_mul]

lemma card_univ_hmat (r D : ℕ) :
    ((Finset.univ : Finset (Fin r → Fin D → ZMod 2)).card : ℝ) = (2:ℝ)^((r:ℝ)*D) := by
  rw [Finset.card_univ, card_fun_zmod_cast]

lemma card_univ_hpair (r D : ℕ) :
    ((Finset.univ : Finset ((Fin r → Fin D → ZMod 2) × (Fin r → Fin D → ZMod 2))).card : ℝ)
      = (2:ℝ)^(2*(r:ℝ)*D) := by
  rw [Finset.card_univ, Fintype.card_prod, Nat.cast_mul, card_fun_zmod_cast, rpow_two_mul]
  congr 1
  ring

/-- Kalachev--Panteleev property `(*)` implies the distance bound: a non-zero codeword is longer
than `α * D`. -/
theorem gb_dist_of_hasStar {D r : ℕ} {α : ℝ} {C : Submodule (ZMod 2) (Fin D → ZMod 2)}
    (hα : 0 < α) (hr : 1 ≤ r) (h : HasStar α r C) :
    ∀ c ∈ C, c ≠ 0 → α * D ≤ hammingNorm c := by
  intro c hc hcne
  by_contra hcon
  push Not at hcon
  have hspan : IsSparse α (Submodule.span (ZMod 2) ({c} : Set (Fin D → ZMod 2))) := by
    refine ⟨{c}, ?_, rfl⟩
    intro v hv
    rw [Set.mem_singleton_iff] at hv
    subst hv
    exact le_of_lt hcon
  have hfrk : frk (Submodule.span (ZMod 2) ({c} : Set (Fin D → ZMod 2))) = 1 := by
    rw [frk, finrank_span_singleton hcne]
  have hle : frk (Submodule.span (ZMod 2) ({c} : Set (Fin D → ZMod 2))) ≤ r := by
    rw [hfrk]; exact hr
  have hstar := h _ hspan (by rw [hfrk]; norm_num) hle
  have hle2 : (Submodule.span (ZMod 2) ({c} : Set (Fin D → ZMod 2))) ≤ C :=
    Submodule.span_le.mpr (by intro v hv; rw [Set.mem_singleton_iff] at hv; subst hv; exact hc)
  have heq : C ⊓ Submodule.span (ZMod 2) ({c} : Set (Fin D → ZMod 2)) =
      Submodule.span (ZMod 2) ({c} : Set (Fin D → ZMod 2)) := inf_eq_right.mpr hle2
  rw [heq, hfrk] at hstar
  omega

lemma nzCols_le {D : ℕ} (x : Fin D × Fin D → ZMod 2) : nzCols x ≤ D := by
  have := Finset.card_filter_le (Finset.univ : Finset (Fin D)) (fun j => ∃ i, x (i, j) ≠ 0)
  simpa [nzCols, Finset.card_univ, Fintype.card_fin] using this

lemma nzRows_le {D : ℕ} (x : Fin D × Fin D → ZMod 2) : nzRows x ≤ D := by
  have := Finset.card_filter_le (Finset.univ : Finset (Fin D)) (fun i => ∃ j, x (i, j) ≠ 0)
  simpa [nzRows, Finset.card_univ, Fintype.card_fin] using this

end Work.LT
