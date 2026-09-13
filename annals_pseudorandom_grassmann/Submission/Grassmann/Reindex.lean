import Submission.Grassmann.FibreCount
import Submission.Commons.Analysis.Sum.stratum_pair_le
import Submission.Commons.Analysis.Sum.stratum_pair_le_sharp

/-!
# The weighted fibre bound of the §8 reindexing (P3)

This file proves the weighted version of the fibre bound `card_fibre3_le`: summing the weight
`2 ^ (26 d·S + C (d−S)² + 3 d·rank Z + 4 d·rank Z)` (where `S = totOrder`) over a fibre of
`Φ₃ : (t,p) ↦ (V₃,W₃,XsOf t p)` costs at most `2 ^ (C d²)` times the factor `2 ^ (−4 d·rank Z)`
that the sharp restricted corollary `XNormSum.sum_inv_pow_sq_l2sq_plLE_le` needs.

The three ingredients are:

* `fiberStratum` — the stratum `(dim V₂, codim W₂)` of a point of the fibre, an element of
  `Fin (d+1) × Fin (d+1)` (finiteness is what makes `Fintype.sum_fiberwise` applicable);
* `fiber_stratum_le` — the per-stratum bound: `card_fibre3_le` plus `weight_eq_of_fiber`;
* `stratum_pair_le` (commons, `Analysis/Sum`) — the arithmetic sum
  `∑_{s=1}^{d} (s+1) 2 ^ (2sd+26ds+7dk+C(d−s)²) ≤ 2 ^ (Cd²−4dk)` for `C ≥ 41`.

Main result: `fiber_weight_le`.
-/

open Finset BigOperators Matrix
open Classical

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

variable {m n : ℕ}

/-! ## The weight of a point of the fibre -/

/-- The weight `2 ^ (26 d·S + C (d−S)² + 3 d·rank(XsOf t p) + 4 d·rank X)` of a point `(t,p)`
of the switching sum, as a function of the point alone. -/
noncomputable def fiberWeight {m n : ℕ} (d C : ℕ) (x : Σ t : Triple m n, QPair m n t) : ℝ :=
  (2 : ℝ) ^ (26 * d * totOrder x.1 + C * (d - totOrder x.1) ^ (2 : ℕ)
    + 3 * d * (XsOf x.1 x.2).rank + 4 * d * Module.finrank 𝔽₂ (LinearMap.range x.1.2.2))

/-! ## The stratum map -/

/-- The stratum `(dim V₂, codim W₂)` of a point of the `Phi3`-fibre, as an element of
`Fin (d+1) × Fin (d+1)`: the codomain has to be finite for `Fintype.sum_fiberwise` to apply, and
`totOrder x ≤ d` bounds both coordinates. -/
noncomputable def fiberStratum (V₀ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Z : Matrix (Fin (n - Module.finrank 𝔽₂ V₀)) (Fin (Module.finrank 𝔽₂ W)) 𝔽₂)
    (d : ℕ) (x : FFib m n V₀ W Z d) : Fin (d + 1) × Fin (d + 1) :=
  (⟨Module.finrank 𝔽₂ x.1.1.1, by
      have h := x.2.2.2.2
      unfold totOrder at h
      omega⟩,
   ⟨m - Module.finrank 𝔽₂ x.1.1.2.1, by
      have h := x.2.2.2.2
      unfold totOrder at h
      omega⟩)

@[simp] lemma fiberStratum_fst_val (V₀ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Z : Matrix (Fin (n - Module.finrank 𝔽₂ V₀)) (Fin (Module.finrank 𝔽₂ W)) 𝔽₂)
    (d : ℕ) (x : FFib m n V₀ W Z d) :
    (fiberStratum V₀ W Z d x).1.1 = Module.finrank 𝔽₂ x.1.1.1 := rfl

@[simp] lemma fiberStratum_snd_val (V₀ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Z : Matrix (Fin (n - Module.finrank 𝔽₂ V₀)) (Fin (Module.finrank 𝔽₂ W)) 𝔽₂)
    (d : ℕ) (x : FFib m n V₀ W Z d) :
    (fiberStratum V₀ W Z d x).2.1 = m - Module.finrank 𝔽₂ x.1.1.2.1 := rfl

/-! ## The `DecidablePred` instances

`FFib` is a subtype of a finite type, so it inherits a `Fintype` instance; but the predicate
involves `Phi3`, `ReindexGood` and `totOrder`, so instance search does not find
`DecidablePred` on its own and the `Fintype` instance has to be supplied explicitly. -/

/-- The `DecidablePred` instance of the defining predicate of `FFib`, which makes `FFib` (and its
subtypes) inherit the `Fintype` instance of `Σ t, QPair m n t`. -/
instance instDecidablePredFFib {m n : ℕ} (V₀ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Z : Matrix (Fin (n - Module.finrank 𝔽₂ V₀)) (Fin (Module.finrank 𝔽₂ W)) 𝔽₂) (d : ℕ) :
    DecidablePred (fun x : Σ t : Triple m n, QPair m n t =>
      Phi3 x = ⟨V₀, W, Z⟩ ∧ ReindexGood d x ∧ 1 ≤ totOrder x.1 ∧ totOrder x.1 ≤ d) :=
  fun _ => inferInstance

/-! ## The fibre of a stratum is empty outside `1 ≤ S ≤ d` -/

/-- A point of the fibre whose stratum is `p` has total order `p.1.1 + p.2.1 + rank Z`; hence it
cannot lie in a stratum with `¬ (S ≤ d ∧ 1 ≤ S)`. -/
lemma fiberStratum_empty (V₀ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Z : Matrix (Fin (n - Module.finrank 𝔽₂ V₀)) (Fin (Module.finrank 𝔽₂ W)) 𝔽₂)
    (d : ℕ) (p : Fin (d + 1) × Fin (d + 1))
    (hp : ¬ (p.1.1 + p.2.1 + Z.rank ≤ d ∧ 1 ≤ p.1.1 + p.2.1 + Z.rank)) :
    IsEmpty {x : FFib m n V₀ W Z d // fiberStratum V₀ W Z d x = p} :=
  ⟨fun y => by
    obtain ⟨z, hz⟩ := y
    have hi : Module.finrank 𝔽₂ z.1.1.1 = p.1.1 := by
      simpa only [fiberStratum] using congrArg (fun q : Fin (d + 1) × Fin (d + 1) => q.1.1) hz
    have hj : m - Module.finrank 𝔽₂ z.1.1.2.1 = p.2.1 := by
      simpa only [fiberStratum] using congrArg (fun q : Fin (d + 1) × Fin (d + 1) => q.2.1) hz
    have ht := totOrder_of_fiber (x := z.1) z.2.1 z.2.2.1 hi hj
    have h1 : 1 ≤ totOrder z.1.1 := z.2.2.2.1
    have h2 : totOrder z.1.1 ≤ d := z.2.2.2.2
    rw [ht, hi, hj] at h1 h2
    exact hp ⟨h2, h1⟩⟩

/-! ## The per-stratum bound -/

/-- **The weighted fibre bound on a single stratum.**  The number of points of the fibre over
`(V₀,W,Z)` at stratum `p` is at most `2 ^ (2 S d)` (`card_fibre3_le`) and the weight is constant on
the stratum and equal to `2 ^ (26 d S + C (d−S)² + 7 d·rank Z)` (`weight_eq_of_fiber`). -/
lemma fiber_stratum_le (V₀ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Z : Matrix (Fin (n - Module.finrank 𝔽₂ V₀)) (Fin (Module.finrank 𝔽₂ W)) 𝔽₂)
    (d C : ℕ) (p : Fin (d + 1) × Fin (d + 1)) :
    (∑ x : {x : FFib m n V₀ W Z d // fiberStratum V₀ W Z d x = p}, fiberWeight d C x.1.1)
      ≤ (2 : ℝ) ^ (2 * (p.1.1 + p.2.1 + Z.rank) * d) *
          (2 : ℝ) ^ (26 * d * (p.1.1 + p.2.1 + Z.rank)
            + C * (d - (p.1.1 + p.2.1 + Z.rank)) ^ (2 : ℕ) + 7 * d * Z.rank) := by
  classical
  haveI hdecFib : DecidablePred (fun x : Σ t : Triple m n, QPair m n t =>
      Phi3 x = ⟨V₀, W, Z⟩ ∧ ReindexGood d x ∧ Module.finrank 𝔽₂ x.1.1 = p.1.1 ∧
        m - Module.finrank 𝔽₂ x.1.2.1 = p.2.1) := fun x => inferInstance
  have hiOf : ∀ z : {x : FFib m n V₀ W Z d // fiberStratum V₀ W Z d x = p},
      Module.finrank 𝔽₂ z.1.1.1.1 = p.1.1 := fun z =>
    (by simpa only [fiberStratum] using
      congrArg (fun q : Fin (d + 1) × Fin (d + 1) => q.1.1) z.2 :
      Module.finrank 𝔽₂ z.1.1.1.1 = p.1.1)
  have hjOf : ∀ z : {x : FFib m n V₀ W Z d // fiberStratum V₀ W Z d x = p},
      m - Module.finrank 𝔽₂ z.1.1.1.2.1 = p.2.1 := fun z =>
    (by simpa only [fiberStratum] using
      congrArg (fun q : Fin (d + 1) × Fin (d + 1) => q.2.1) z.2 :
      m - Module.finrank 𝔽₂ z.1.1.1.2.1 = p.2.1)
  by_cases hps : p.1.1 + p.2.1 + Z.rank ≤ d
  · have hval : ∀ z : {x : FFib m n V₀ W Z d // fiberStratum V₀ W Z d x = p},
        fiberWeight d C z.1.1 = (2 : ℝ) ^ (26 * d * (p.1.1 + p.2.1 + Z.rank)
          + C * (d - (p.1.1 + p.2.1 + Z.rank)) ^ (2 : ℕ) + 7 * d * Z.rank) := by
      intro z
      have hw := weight_eq_of_fiber (V₀ := V₀) (W := W) (Z := Z) (d := d) (C := C)
        (i := p.1.1) (j := p.2.1) (x := z.1.1) z.1.2.1 z.1.2.2.1 (hiOf z) (hjOf z)
      unfold fiberWeight
      rw [hw, hiOf z, hjOf z]
      congr 1
      ring
    have hinj : Function.Injective
        (fun z : {x : FFib m n V₀ W Z d // fiberStratum V₀ W Z d x = p} =>
          (⟨z.1.1, ⟨z.1.2.1, z.1.2.2.1, hiOf z, hjOf z⟩⟩ :
            Fibre3 m n V₀ W Z d p.1.1 p.2.1)) := by
      intro a b hab
      have h1 : a.1.1 = b.1.1 :=
        congrArg (fun y : Fibre3 m n V₀ W Z d p.1.1 p.2.1 => y.1) hab
      exact Subtype.ext (Subtype.ext h1)
    have hcard : Fintype.card {x : FFib m n V₀ W Z d // fiberStratum V₀ W Z d x = p}
        ≤ 2 ^ (2 * (p.1.1 + p.2.1 + Z.rank) * d) := by
      refine (Fintype.card_le_of_injective _ hinj).trans ?_
      rw [← Nat.card_eq_fintype_card]
      exact card_fibre3_le V₀ W Z d p.1.1 p.2.1 hps
    calc (∑ z : {x : FFib m n V₀ W Z d // fiberStratum V₀ W Z d x = p}, fiberWeight d C z.1.1)
        = ∑ _z : {x : FFib m n V₀ W Z d // fiberStratum V₀ W Z d x = p},
            (2 : ℝ) ^ (26 * d * (p.1.1 + p.2.1 + Z.rank)
              + C * (d - (p.1.1 + p.2.1 + Z.rank)) ^ (2 : ℕ) + 7 * d * Z.rank) :=
          Finset.sum_congr rfl (fun z _ => hval z)
      _ = (Fintype.card {x : FFib m n V₀ W Z d // fiberStratum V₀ W Z d x = p} : ℝ) *
            (2 : ℝ) ^ (26 * d * (p.1.1 + p.2.1 + Z.rank)
              + C * (d - (p.1.1 + p.2.1 + Z.rank)) ^ (2 : ℕ) + 7 * d * Z.rank) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ (2 : ℝ) ^ (2 * (p.1.1 + p.2.1 + Z.rank) * d) *
            (2 : ℝ) ^ (26 * d * (p.1.1 + p.2.1 + Z.rank)
              + C * (d - (p.1.1 + p.2.1 + Z.rank)) ^ (2 : ℕ) + 7 * d * Z.rank) := by
          gcongr
          exact_mod_cast hcard
  · have hEmpty := fiberStratum_empty V₀ W Z d p (by omega)
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    positivity

/-! ## P3: the weighted fibre bound -/

/-- **P3 — the weighted fibre bound.**  The sum of the weights of the points of a fibre of `Φ₃`
is at most `2 ^ (C d²)` times the factor `2 ^ (−4 d·rank Z)` of the sharp restricted corollary. -/
theorem fiber_weight_le_aux (V₀ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Z : Matrix (Fin (n - Module.finrank 𝔽₂ V₀)) (Fin (Module.finrank 𝔽₂ W)) 𝔽₂)
    (d C : ℕ) {R : ℝ}
    (harith : (∑ i : Fin (d + 1), ∑ j : Fin (d + 1),
      (if i.1 + j.1 + Z.rank ≤ d ∧ 1 ≤ i.1 + j.1 + Z.rank then
        (2 : ℝ) ^ (2 * (i.1 + j.1 + Z.rank) * d) *
          (2 : ℝ) ^ (26 * d * (i.1 + j.1 + Z.rank)
            + C * (d - (i.1 + j.1 + Z.rank)) ^ (2 : ℕ) + 7 * d * Z.rank)
      else 0)) ≤ R) :
    (∑ x : FFib m n V₀ W Z d, fiberWeight d C x.1) ≤ R := by
  classical
  have hfiber : (∑ x : FFib m n V₀ W Z d, fiberWeight d C x.1)
      = ∑ p : Fin (d + 1) × Fin (d + 1),
          ∑ z : {x : FFib m n V₀ W Z d // fiberStratum V₀ W Z d x = p},
            fiberWeight d C z.1.1 :=
    (Fintype.sum_fiberwise (fiberStratum V₀ W Z d)
      (fun x : FFib m n V₀ W Z d => fiberWeight d C x.1)).symm
  rw [hfiber]
  have hper : ∀ p : Fin (d + 1) × Fin (d + 1),
      (∑ z : {x : FFib m n V₀ W Z d // fiberStratum V₀ W Z d x = p}, fiberWeight d C z.1.1) ≤
        (if p.1.1 + p.2.1 + Z.rank ≤ d ∧ 1 ≤ p.1.1 + p.2.1 + Z.rank then
          (2 : ℝ) ^ (2 * (p.1.1 + p.2.1 + Z.rank) * d) *
            (2 : ℝ) ^ (26 * d * (p.1.1 + p.2.1 + Z.rank)
              + C * (d - (p.1.1 + p.2.1 + Z.rank)) ^ (2 : ℕ) + 7 * d * Z.rank)
        else 0) := by
    intro p
    by_cases hp : p.1.1 + p.2.1 + Z.rank ≤ d ∧ 1 ≤ p.1.1 + p.2.1 + Z.rank
    · rw [if_pos hp]
      exact fiber_stratum_le V₀ W Z d C p
    · rw [if_neg hp]
      have hEmpty := fiberStratum_empty V₀ W Z d p hp
      rw [Finset.univ_eq_empty, Finset.sum_empty]
  refine (Finset.sum_le_sum (fun p _ => hper p)).trans ?_
  rw [Fintype.sum_prod_type]
  exact harith

/-- **P3 — the weighted fibre bound.**  The sum of the weights of the points of a fibre of `Φ₃`
is at most `2 ^ (C d²)` times the factor `2 ^ (−4 d·rank Z)` of the sharp restricted corollary. -/
theorem fiber_weight_le (V₀ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Z : Matrix (Fin (n - Module.finrank 𝔽₂ V₀)) (Fin (Module.finrank 𝔽₂ W)) 𝔽₂)
    (d C : ℕ) (hC : 41 ≤ C) :
    (∑ x : FFib m n V₀ W Z d, fiberWeight d C x.1)
      ≤ (2 : ℝ) ^ (C * d ^ 2) * ((2 : ℝ) ^ (4 * d * Z.rank))⁻¹ :=
  fiber_weight_le_aux V₀ W Z d C (Commons.Analysis.Sum.stratum_pair_le C d Z.rank hC)

/-- **P3, strengthened by `λ d k`**: the conclusion is `2 ^ (C d²) · (2 ^ (12 d k))⁻¹`, which is
what the removal of the extra `D_X`-derivatives (whose honest loss is `2 ^ (7 d k)` per rank
stratum) needs. -/
theorem fiber_weight_le_sharp (V₀ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Z : Matrix (Fin (n - Module.finrank 𝔽₂ V₀)) (Fin (Module.finrank 𝔽₂ W)) 𝔽₂)
    (d C : ℕ) (hC : 51 ≤ C) :
    (∑ x : FFib m n V₀ W Z d, fiberWeight d C x.1)
      ≤ (2 : ℝ) ^ (C * d ^ 2) * ((2 : ℝ) ^ (12 * d * Z.rank))⁻¹ :=
  fiber_weight_le_aux V₀ W Z d C (Commons.Analysis.Sum.stratum_pair_le_sharp C d Z.rank hC)


/-! ## The strengthened fibre bound with an index-independent shave -/

/-- Auxiliary arithmetic estimate (the `d`-shave form): for `1 ≤ s ≤ d`, `k ≤ s` and `61 ≤ C`,
`2 s d + (26 d s + C (d−s)² + 7 d k) + 12 d k + 12 d ≤ C d² − 2 d`.

This is `key_arith_sharp` of the commons lemma `Commons.Analysis.Sum.stratum_pair_le_sharp` with
the additional cost `12 d + 2 d` (the `2 d` pays for the `(d+1)²` summation count), which is
affordable because `61 ≥ 47 + 14`. -/
lemma key_arith_dshave (C d s k : ℕ) (hC : 61 ≤ C) (hs1 : 1 ≤ s) (hsd : s ≤ d) (hks : k ≤ s) :
    2 * s * d + (26 * d * s + C * (d - s) ^ 2 + 7 * d * k) + 12 * d * k + 12 * d
      ≤ C * d ^ 2 - 2 * d := by
  have hmain : 28 * d * s + C * (d - s) ^ 2 + 19 * d * k + 14 * d ≤ C * d ^ 2 := by
    obtain ⟨m, hm⟩ : ∃ m, d = m + s := ⟨d - s, by omega⟩
    rw [hm]
    simp only [Nat.add_sub_cancel]
    have hk : 19 * (m + s) * k ≤ 19 * (m + s) * s := Nat.mul_le_mul_left _ hks
    have h61 : (61 : ℕ) ≤ C := hC
    have hCsq : 61 * (2 * m * s + s ^ 2) ≤ C * (2 * m * s + s ^ 2) :=
      Nat.mul_le_mul_right _ h61
    nlinarith [hk, hCsq, hs1, Nat.zero_le m]
  have he : 2 * s * d + (26 * d * s + C * (d - s) ^ 2 + 7 * d * k) + 12 * d * k + 12 * d + 2 * d
      = 28 * d * s + C * (d - s) ^ 2 + 19 * d * k + 14 * d := by ring
  rw [← he] at hmain
  exact Nat.le_sub_of_add_le hmain

/-- **The weighted stratum sum with a `d`-shave**: the same sum as
`Commons.Analysis.Sum.stratum_pair_le_sharp`, with the additional factor `2 ^ (−12 d)`.

The extra `d`-shave is what lets the final step of the induction absorb the constant `162` of
`after_restricting'` (the paper's `q^{-31d}`, which is independent of the summation index). -/
theorem stratum_pair_le_dshave (C d k : ℕ) (hC : 61 ≤ C) :
    (∑ i : Fin (d + 1), ∑ j : Fin (d + 1),
      (if i.1 + j.1 + k ≤ d ∧ 1 ≤ i.1 + j.1 + k then
        (2 : ℝ) ^ (2 * (i.1 + j.1 + k) * d) *
          (2 : ℝ) ^ (26 * d * (i.1 + j.1 + k) + C * (d - (i.1 + j.1 + k)) ^ 2 + 7 * d * k)
      else 0))
      ≤ (2 : ℝ) ^ (C * d ^ 2) * ((2 : ℝ) ^ (12 * d * k + 12 * d))⁻¹ := by
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  have hterm : ∀ i j : Fin (d + 1),
      (if i.1 + j.1 + k ≤ d ∧ 1 ≤ i.1 + j.1 + k then
        (2 : ℝ) ^ (2 * (i.1 + j.1 + k) * d) *
          (2 : ℝ) ^ (26 * d * (i.1 + j.1 + k) + C * (d - (i.1 + j.1 + k)) ^ 2 + 7 * d * k)
      else 0) * (2 : ℝ) ^ (12 * d * k + 12 * d) ≤ (2 : ℝ) ^ (C * d ^ 2 - 2 * d) := by
    intro i j
    set s := i.1 + j.1 + k with hs
    split_ifs with h
    · obtain ⟨hsd, hs1⟩ := h
      have hks : k ≤ s := by rw [hs]; omega
      have hrew : (2 : ℝ) ^ (2 * s * d) *
            (2 : ℝ) ^ (26 * d * s + C * (d - s) ^ 2 + 7 * d * k) * (2 : ℝ) ^ (12 * d * k + 12 * d)
          = (2 : ℝ) ^ ((2 * s * d + (26 * d * s + C * (d - s) ^ 2 + 7 * d * k))
              + (12 * d * k + 12 * d)) := by
        rw [← pow_add, ← pow_add]
      rw [hrew]
      apply pow_le_pow_right₀ (by norm_num)
      have he2 : (2 * s * d + (26 * d * s + C * (d - s) ^ 2 + 7 * d * k))
            + (12 * d * k + 12 * d)
          = 2 * s * d + (26 * d * s + C * (d - s) ^ 2 + 7 * d * k) + 12 * d * k + 12 * d := by
        ring
      rw [he2]
      exact key_arith_dshave C d s k hC hs1 hsd hks
    · rw [zero_mul]; positivity
  have hcount : (((d + 1 : ℕ) : ℝ)) * (((d + 1 : ℕ) : ℝ)) ≤ (2 : ℝ) ^ (2 * d) := by
    have hle : (((d + 1 : ℕ) : ℝ)) ≤ (2 : ℝ) ^ d := by
      have hd : d < 2 ^ d := Nat.lt_two_pow_self
      exact_mod_cast (Nat.succ_le_of_lt hd)
    calc (((d + 1 : ℕ) : ℝ)) * (((d + 1 : ℕ) : ℝ)) = (((d + 1 : ℕ) : ℝ)) ^ 2 := by ring
      _ ≤ ((2 : ℝ) ^ d) ^ 2 := pow_le_pow_left₀ (by positivity) hle 2
      _ = (2 : ℝ) ^ (2 * d) := by rw [← pow_mul]; congr 1; ring
  have h2 : 2 * d ≤ C * d ^ 2 := by
    rcases Nat.eq_zero_or_pos d with hd | hd
    · rw [hd]; simp
    · nlinarith [hC, hd]
  have hsum2 : 2 * d + (C * d ^ 2 - 2 * d) = C * d ^ 2 := by omega
  simp_rw [Finset.sum_mul]
  calc (∑ i : Fin (d + 1), ∑ j : Fin (d + 1),
          (if i.1 + j.1 + k ≤ d ∧ 1 ≤ i.1 + j.1 + k then
            (2 : ℝ) ^ (2 * (i.1 + j.1 + k) * d) *
              (2 : ℝ) ^ (26 * d * (i.1 + j.1 + k) + C * (d - (i.1 + j.1 + k)) ^ 2 + 7 * d * k)
          else 0) * (2 : ℝ) ^ (12 * d * k + 12 * d))
      ≤ ∑ i : Fin (d + 1), ∑ j : Fin (d + 1), (2 : ℝ) ^ (C * d ^ 2 - 2 * d) := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        exact hterm i j
    _ = (((d + 1 : ℕ) : ℝ) * ((d + 1 : ℕ) : ℝ)) * (2 : ℝ) ^ (C * d ^ 2 - 2 * d) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
    _ ≤ (2 : ℝ) ^ (2 * d) * (2 : ℝ) ^ (C * d ^ 2 - 2 * d) :=
        mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = (2 : ℝ) ^ (C * d ^ 2) := by rw [← pow_add, hsum2]

/-- **P3 strengthened by both `12 d k` and `12 d`**: the weighted fibre bound with an extra
index-independent shave `2 ^ (−12 d)`. -/
theorem fiber_weight_le_sharp2 (V₀ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Z : Matrix (Fin (n - Module.finrank 𝔽₂ V₀)) (Fin (Module.finrank 𝔽₂ W)) 𝔽₂)
    (d C : ℕ) (hC : 61 ≤ C) :
    (∑ x : FFib m n V₀ W Z d, fiberWeight d C x.1)
      ≤ (2 : ℝ) ^ (C * d ^ 2) * ((2 : ℝ) ^ (12 * d * Z.rank + 12 * d))⁻¹ :=
  fiber_weight_le_aux V₀ W Z d C (stratum_pair_le_dshave C d Z.rank hC)

end
end Submission.Grassmann
