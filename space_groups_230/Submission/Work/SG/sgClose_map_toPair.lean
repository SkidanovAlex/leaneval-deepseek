import Mathlib
import Submission.Work.SG.SGprelude
import Submission.Work.SG.SGinfra
import Submission.Work.SG.sgMulPair_toPair

/-!
# `sgClose_map_toPair`: the `ℚ`-side closure is the image of the `ℤ`-side one

`sgClose gens k acc` is the (`k`-fold) breadth-first closure of the affine generators `gens`
over `ℚ` (`Defs`), started from `acc`; `zClose gens d k acc` is its exact integer mirror at
denominator `d` (`SGprelude`), where the pair `(A, u)` denotes the (representative of the)
affine map `x ↦ A x + u/d` and the translation reduction `Int.fract (·)` is replaced by
`· % d`.  `toPair d (A, u) = (A, u/d)` relates the two (`toPairL`, `divQ`).

This file proves that the two closures are *the same list*, up to `toPair d`:

`sgClose (l.map (toPair d)) k (acc.map (toPair d)) = (zClose l d k acc).map (toPair d)`.

Because both closures are the `k`-fold iteration of one round (`sgF` / `zF`), the whole content
is the one-round statement `sgF_map_toPair`, plus the fact that `toPair d` commutes with
`List.dedup` — which is exactly injectivity of `toPair d`, available by `0 < d`
(`toPair_injective`).  One round is then pure `List` bookkeeping: `toPair` distributes over
`++`, over `flatMap` (`List.map_append`, `List.map_flatMap`, `List.flatMap_map`), and the
product of one pair commutes with `toPair` by `sgMulPair_toPair` (`zMul` is its integer mirror).

Note that the hypothesis `0 < d` is used *only* for injectivity of `toPair d` (equivalently of
`divQ d`); everything else holds for every `d`.
-/

namespace Work.SG

/-- `n ↦ n/d` is injective as soon as `d > 0`.  (For `d = 0` it is the constant map `0`.) -/
theorem divQ_injective {d : ℕ} (hd : 0 < d) : Function.Injective (divQ d) := by
  intro a b h
  have hd0 : (d : ℚ) ≠ 0 := by positivity
  simp only [divQ] at h
  have h' : (a : ℚ) = (b : ℚ) := (div_left_inj' hd0).mp h
  exact_mod_cast h'

/-- `toPair d` is injective as soon as `d > 0` (the matrix part is unchanged, the translation
part is scaled by the injective map `divQ d`). -/
theorem toPair_injective {d : ℕ} (hd : 0 < d) : Function.Injective (toPair d) := by
  intro p q h
  obtain ⟨A, u⟩ := p
  obtain ⟨B, v⟩ := q
  have h1 : A = B := congrArg Prod.fst h
  have h2 : u.map (divQ d) = v.map (divQ d) := congrArg Prod.snd h
  have h3 : u = v := List.map_injective_iff.mpr (divQ_injective hd) h2
  rw [h3, h1]

/-- One closure round commutes with `toPair d`: the `ℚ`-side round on the `toPair`-images is
the `toPair`-image of the integer round.

After unwinding `sgF`/`zF` this is bookkeeping of `List.map` over `++`, `flatMap` and `dedup`,
together with `sgMulPair_toPair` for the products.  The `dedup` step is where injectivity of
`toPair d` (that is, `0 < d`) is used, via `List.dedup_map_of_injective`. -/
theorem sgF_map_toPair {d : ℕ} (hd : 0 < d) (l acc : List (List ℤ × List ℤ)) :
    sgF (l.map (toPair d)) (acc.map (toPair d)) = (zF l d acc).map (toPair d) := by
  have hf : Function.Injective (toPair d) := toPair_injective hd
  -- the `flatMap` parts agree, since one product commutes with `toPair`
  have hB : List.flatMap (fun a => List.map (fun g => sgMulPair a g) (List.map (toPair d) l))
        (List.map (toPair d) acc)
      = List.flatMap (fun a => List.map (toPair d) (List.map (fun g => zMul d a g) l)) acc := by
    rw [List.flatMap_map]
    apply List.flatMap_congr
    intro a _
    have hfun : (fun g => sgMulPair (toPair d a) g) ∘ (toPair d)
        = (toPair d) ∘ (fun g => zMul d a g) := by
      funext g
      simp only [Function.comp_apply]
      exact sgMulPair_toPair d a g
    rw [List.map_map, List.map_map, hfun]
  rw [zF, sgF,
    ← List.dedup_map_of_injective hf (acc ++ acc.flatMap fun a => l.map fun g => zMul d a g),
    List.map_append, List.map_flatMap]
  rw [hB]

/-- The `ℚ`-side closure is the `toPair`-image of the integer closure. -/
theorem sgClose_map_toPair {d : ℕ} (hd : 0 < d) (l acc : List (List ℤ × List ℤ)) (k : ℕ) :
    sgClose (l.map (toPair d)) k (acc.map (toPair d)) = (zClose l d k acc).map (toPair d) := by
  induction k generalizing acc with
  | zero => rfl
  | succ k ih =>
      rw [sgClose_succ, zClose_succ, ih acc, sgF_map_toPair hd l (zClose l d k acc)]

end Work.SG
