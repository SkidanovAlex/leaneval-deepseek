import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseK15.Derive
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseK15.chi_sums_of_decay` — the two `χ̂²`-sums of K2

`Work.BoseB7A.Q3Kernel` asks for the two lattice sums (`Work.BoseB7A.Defs` §5)

* `sum_hatChiSq` : `∑_{s∈excited}|χ̂²_s| ≤ K₀`,
* `tail_hatChiSq`: `∑_{s∈excited}|χ̂²_s|(1 - f_L(s)) ≤ K₀(K_ℓK_L)^{-M}`,

i.e. FS `lem:DecaychiHat` (`|χ̂²(p)| ≤ C(1+‖p‖²)^{-M̃}`) summed over the box modes.
The mode labels are *dual-lattice* points (`hlat`):
`ℓ • kmom s = vec (lift s) = 2π·(lift s)`, so both sums are truncated lattice sums
and are bounded by the two fields of `K15Input` (`sum_geom`, with the `decayOrder`
weight, and `sum_geom_tail`, with the `intM` tail exponent).  The first conjunct is
the `Csum` row, the second the `Ctail` row of the bundle, and both are dominated
by the single `K₀` (`K₀_sum`).

## ⚠ The delegated statement needs `0 < E.Kl * E.KL`

**The statement of `chi_sums_of_decay` as delegated is not provable: the second
conjunct is missing the hypothesis `0 < E.Kl * E.KL`** — FS's side condition
`K_ℓK_L ≥ 1` (`BOSE_3Q_LEAD.md` S10; at FS's parameters `K_ℓK_L = X^{-12} ≥ 1`).

The second conjunct is a case split on the radius `R = E.Kl * E.KL`, and the
`sum_geom_tail` row is only stated for radii `R ≥ 1`, so:

* `1 ≤ R` — the tail row applies and gives exactly the claimed `R^{-intM}`;
  `tail_hatChiSq_le_of_one_le`;
* `0 < R < 1` — `R^{-M} ≥ 1`, so the first conjunct suffices (`1 - f_L ∈ [0,1]`);
  the two cases together are `tail_hatChiSq_le_of_pos`;
* `R ≤ 0` — **not** covered, and **not** excluded by any field of `K15Input`:
  `E.Kl` occurs in `K15Input` *only* on the right-hand side of the field `ellKL`,
  and `E.KL` only in `ellKL`, `fL_supp`, `fL_eq_one`.  If `E.KL ≤ 0` then
  `K_L√(μa) ≤ 0`, and `fL_supp` (`fLf p ≠ 0 → ‖p‖ ≤ K_L√(μa)`) forces `f_L ≡ 0`
  on the excited modes (`fL_eq_zero_of_KL_nonpos`); so the second conjunct is
  *equivalent* to `∑_{s∈excited}|χ̂²_s| ≤ K₀·R^{-M}`
  (`snd_conjunct_iff_of_KL_nonpos`).  At `E.KL = 0` (the identity `ellKL` then
  holds for **every** `E.Kl`: `ℓ·0·√(μa) = 0 = K_ℓ·0`) its right-hand side is
  `K₀·(0:ℝ)^{-M} = 0` for `M = E.intM ≥ 1` (`Real.zero_rpow`), and `hM` only
  bounds `M` from *above* by `49`, so `M ≥ 1` is allowed: the conjunct then
  literally demands `∑_{s∈excited}|χ̂²_s| = 0`
  (`snd_conjunct_iff_sum_eq_zero_of_KL_eq_zero`).  For `E.KL < 0` the right-hand
  side is `K₀·R^{-M}` with `R = E.Kl·E.KL < 0`, i.e. `K₀·|R|^{-M}·(-1)^M`
  (`Real.rpow_def_of_nonpos`), which is `≤ 0` for odd `M` and `< K₀` for large
  `|R|` — again below the (non-negative) left-hand side.

  Such a demand is *not* a consequence of `K15Input`: it is a statement about the
  values `χ̂²(ℓ·kmom s) = χ̂²(2π·lift s)` of the localization function, and those
  are non-zero at some non-zero lattice points.  Indeed the mode labels
  `ℓ • kmom s = 2π·(lift s)` are always **non-zero** lattice points, while
  `χ̂²(2π·)` does not vanish on all of them: `χ̂²` is the Fourier transform of the
  compactly supported `χ²`, so by Poisson summation
  `∑_{n∈ℤ³} χ̂²(2πn) = ∑_{m∈ℤ³} χ(m)² = χ(0)² = 1/chiNormSq > 1` while
  `χ̂²(0) = ∫χ² = 1`, hence some `n ≠ 0` has `χ̂²(2πn) ≠ 0`.  The remaining rows
  of `K15Input` are satisfiable in the degenerate regime (`Ŵ₁ = Ŵ₁ω = ĝ = 0`,
  `ρ_z = 0`, `K_H·a` small so that `P_H` is empty and all four `P_H`-lattice sums
  are empty sums, the analytic rows reducing to trivial non-negativity), so no
  hypothesis of the statement rules the configuration out.

*At the intended call site the missing hypothesis is already available*:
`Submission/Work/BoseK15/Corpus.lean` invokes `chi_sums_of_decay h h.ellKL
(intM_add_three_le (E := E) hv)` in a context with `hv : FSParamsView E`, and the
ninth conjunct `hS9` of `Work.BoseB7A.smallness_ratios` is *literally*
`1 ≤ E.Kl * E.KL` (it is already passed to the sibling `count_PL_le`, and it is
not used by any other hypothesis of this lemma).  So the minimal repair is to add
`(hKL : 1 ≤ E.Kl * E.KL)` — as `count_PL_le` does — or to record the S10 side
condition in the `K15Input` bundle.  Concretely, the call sites become

```
  obtain ⟨hsum, htail⟩ :=
    chi_sums_of_decay_of_one_le_KlKL h h.ellKL (intM_add_three_le (E := E) hv) hS9
```

(one extra argument `hS9`); no other change is needed.

The corrected statements are proved sorry-free below (this file has **no** `sorry`):

* `chi_sums_of_decay_of_pos_KlKL` — with the sharp hypothesis `0 < E.Kl * E.KL`;
* `chi_sums_of_decay_of_one_le_KlKL` — with `1 ≤ E.Kl * E.KL`, i.e. exactly the
  hypothesis available at the call site (the form of `count_PL_le`).

The degeneracy is made formal by `fL_eq_zero_of_KL_nonpos`,
`snd_conjunct_iff_of_KL_nonpos` and `snd_conjunct_iff_sum_eq_zero_of_KL_eq_zero`.
The delegated statement itself is reproduced verbatim at the
end of the file.
-/

noncomputable section

open scoped BigOperators Pointwise
open MeasureTheory Classical

namespace Work.BoseK15

open Work.BoseB7 Work.BoseB7A

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
variable {F : FockData Mode} {T : TildeData F} {E : Q3Env Mode} {K₀ : ℝ}

/-! ## 1. The lattice weight of the decay sum -/

/-- The lattice weight `(1 + ‖vec n‖²)^{-decayOrder}` of `K15Input.sum_geom`. -/
noncomputable def latticeWeight (n : Fin 3 → ℤ) : ℝ :=
  (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ decayOrder)⁻¹

lemma latticeWeight_nonneg (n : Fin 3 → ℤ) : 0 ≤ latticeWeight n :=
  inv_nonneg.mpr (pow_nonneg (by positivity) _)

lemma latticeWeight_pos (n : Fin 3 → ℤ) : 0 < latticeWeight n :=
  inv_pos.mpr (pow_pos (by positivity) _)

/-! ## 2. The two sums from the `K15Input` lattice rows -/

namespace K15Input

/-- **The lattice label of a mode.**  `ℓ • kmom s` is the lattice momentum
`vec (lift s) = 2π·(lift s)`: the argument at which `χ̂²` is evaluated on the mode
`s` (`hatChiSq_eq`). -/
theorem ell_smul_kmom (h : K15Input K₀ F T E) (s : Mode) :
    h.ell • h.kmom s = Work.BoseB4.vec (h.hlat.lift s) := by
  rw [h.hlat.lift_spec s, smul_smul, mul_inv_cancel₀ (ne_of_gt h.ell_pos), one_smul]

/-- FS `lem:DecaychiHat` at the mode `s`, in lattice coordinates. -/
theorem hatChiSq_abs_le_lift (h : K15Input K₀ F T E) (s : Mode) :
    |E.hatChiSq s| ≤ h.Cchi * latticeWeight (h.hlat.lift s) := by
  rw [h.hatChiSq_eq s, ← h.ell_eq_E, h.ell_smul_kmom s]
  exact h.hatChiSq_abs_le _

/-- The `Csum` row: `∑_{s∈excited}|χ̂²_s| ≤ Cchi·Csum`. -/
theorem sum_hatChiSq_le_Csum (h : K15Input K₀ F T E) :
    ∑ s ∈ excited Mode, |E.hatChiSq s| ≤ h.Cchi * h.Csum := by
  calc ∑ s ∈ excited Mode, |E.hatChiSq s|
      ≤ ∑ s ∈ excited Mode, h.Cchi * latticeWeight (h.hlat.lift s) :=
        Finset.sum_le_sum (fun s _ => h.hatChiSq_abs_le_lift s)
    _ = h.Cchi * ∑ n ∈ (excited Mode).image h.hlat.lift, latticeWeight n := by
        rw [Finset.mul_sum]
        exact (Finset.sum_image (s := excited Mode) (g := h.hlat.lift)
          (f := fun n => h.Cchi * latticeWeight n)
          (fun a _ b _ hab => h.hlat.lift_injective hab)).symm
    _ ≤ h.Cchi * h.Csum := mul_le_mul_of_nonneg_left (h.sum_geom _) h.Cchi_nonneg

/-- **The first conjunct**: `∑_{s∈excited}|χ̂²_s| ≤ K₀`. -/
theorem sum_hatChiSq_le (h : K15Input K₀ F T E) :
    ∑ s ∈ excited Mode, |E.hatChiSq s| ≤ K₀ := by
  refine h.sum_hatChiSq_le_Csum.trans ?_
  calc h.Cchi * h.Csum ≤ h.Cchi * (h.Csum + h.Ctail) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right h.Ctail_nonneg) h.Cchi_nonneg
    _ ≤ K₀ := h.K₀_sum

/-- **The tail sum, for `1 ≤ K_ℓK_L`.**  The terms with `f_L s = 1` vanish (`f_L
= 1` on `P_L`); the remaining modes label lattice points *outside* the ball of
radius `K_ℓK_L` (`f_L` is supported in `P_L` and `ℓK_L√(μa) = K_ℓK_L`), and the
tail lattice row `sum_geom_tail` finishes. -/
theorem tail_hatChiSq_le_of_one_le (h : K15Input K₀ F T E)
    (hell : h.ell * E.KL * Real.sqrt (E.mu * E.aScat) = E.Kl * E.KL)
    (hKL : 1 ≤ E.Kl * E.KL) :
    ∑ s ∈ excited Mode, |E.hatChiSq s| * (1 - E.fL s)
      ≤ K₀ * (E.Kl * E.KL) ^ (-(E.intM : ℝ)) := by
  set R : ℝ := E.Kl * E.KL with hRdef
  have hRpos : 0 < R := lt_of_lt_of_le one_pos hKL
  -- (1) the terms with `f_L s = 1` vanish
  have hred : ∑ s ∈ excited Mode, |E.hatChiSq s| * (1 - E.fL s)
      = ∑ s ∈ (excited Mode).filter (fun s => E.fL s ≠ 1),
          |E.hatChiSq s| * (1 - E.fL s) := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro s hs hns
    have h1 : E.fL s = 1 := by
      by_contra hne
      exact hns (Finset.mem_filter.mpr ⟨hs, hne⟩)
    simp [h1]
  -- (2) each remaining term is at most the pointwise χ̂²-decay
  have hterm : ∀ s ∈ (excited Mode).filter (fun s => E.fL s ≠ 1),
      |E.hatChiSq s| * (1 - E.fL s) ≤ h.Cchi * latticeWeight (h.hlat.lift s) := by
    intro s _
    have h1 : 0 ≤ 1 - E.fL s := by linarith [h.fL_le_one_holds s]
    have h2 : 1 - E.fL s ≤ 1 := by linarith [h.fL_nonneg_holds s]
    calc |E.hatChiSq s| * (1 - E.fL s)
        ≤ (h.Cchi * latticeWeight (h.hlat.lift s)) * 1 :=
          mul_le_mul (h.hatChiSq_abs_le_lift s) h2 h1
            (mul_nonneg h.Cchi_nonneg (latticeWeight_nonneg _))
      _ = h.Cchi * latticeWeight (h.hlat.lift s) := by ring
  -- (3) the remaining modes label lattice points of norm `> R = K_ℓK_L`
  let S : Finset (Fin 3 → ℤ) :=
    ((excited Mode).filter (fun s => E.fL s ≠ 1)).image h.hlat.lift
  have hnorm : ∀ n ∈ S, R ≤ ‖Work.BoseB4.vec n‖ := by
    intro n hn
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hn
    have hfL : E.fL s ≠ 1 := (Finset.mem_filter.mp hs).2
    have hgt : E.KL * Real.sqrt (E.mu * E.aScat) < ‖h.kmom s‖ := by
      by_contra hle
      exact hfL (by rw [h.fL_eq s]; exact h.fL_eq_one _ (le_of_not_gt hle))
    have h3 : h.ell * (E.KL * Real.sqrt (E.mu * E.aScat)) = R := by
      rw [hRdef, ← mul_assoc]; exact hell
    rw [← h.ell_smul_kmom s, norm_smul, Real.norm_eq_abs, abs_of_pos h.ell_pos, ← h3]
    exact le_of_lt (mul_lt_mul_of_pos_left hgt h.ell_pos)
  -- (4) the tail lattice row
  have htail : ∑ n ∈ S, latticeWeight n ≤ h.Ctail / R ^ E.intM :=
    h.sum_geom_tail R S hKL hnorm
  have hCchiCtail : h.Cchi * h.Ctail ≤ K₀ := by
    calc h.Cchi * h.Ctail ≤ h.Cchi * (h.Csum + h.Ctail) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_left h.Csum_nonneg) h.Cchi_nonneg
      _ ≤ K₀ := h.K₀_sum
  calc ∑ s ∈ excited Mode, |E.hatChiSq s| * (1 - E.fL s)
      = ∑ s ∈ (excited Mode).filter (fun s => E.fL s ≠ 1),
          |E.hatChiSq s| * (1 - E.fL s) := hred
    _ ≤ ∑ s ∈ (excited Mode).filter (fun s => E.fL s ≠ 1),
          h.Cchi * latticeWeight (h.hlat.lift s) := Finset.sum_le_sum hterm
    _ = h.Cchi * ∑ n ∈ S, latticeWeight n := by
        rw [Finset.mul_sum]
        exact (Finset.sum_image (s := (excited Mode).filter (fun s => E.fL s ≠ 1))
          (g := h.hlat.lift) (f := fun n => h.Cchi * latticeWeight n)
          (fun a _ b _ hab => h.hlat.lift_injective hab)).symm
    _ ≤ h.Cchi * (h.Ctail / R ^ E.intM) := mul_le_mul_of_nonneg_left htail h.Cchi_nonneg
    _ = (h.Cchi * h.Ctail) / R ^ E.intM := by ring
    _ ≤ K₀ / R ^ E.intM := div_le_div_of_nonneg_right hCchiCtail (by positivity)
    _ = K₀ * R ^ (-(E.intM : ℝ)) := by
        rw [div_eq_mul_inv, ← Real.rpow_natCast R E.intM, ← Real.rpow_neg (le_of_lt hRpos)]
    _ = K₀ * (E.Kl * E.KL) ^ (-(E.intM : ℝ)) := by rw [hRdef]

/-- **The tail sum, for `0 < K_ℓK_L`** (the sharp hypothesis).  The two branches of
the case split are `R ≥ 1`, where the `Ctail` row applies, and `0 < R < 1`, where
`R^{-M} ≥ 1` so that the *first* conjunct, `∑|χ̂²_s| ≤ K₀`, already suffices. -/
theorem tail_hatChiSq_le_of_pos (h : K15Input K₀ F T E)
    (hell : h.ell * E.KL * Real.sqrt (E.mu * E.aScat) = E.Kl * E.KL)
    (hR : 0 < E.Kl * E.KL) :
    ∑ s ∈ excited Mode, |E.hatChiSq s| * (1 - E.fL s)
      ≤ K₀ * (E.Kl * E.KL) ^ (-(E.intM : ℝ)) := by
  rcases le_total 1 (E.Kl * E.KL) with h1 | h1
  · exact h.tail_hatChiSq_le_of_one_le hell h1
  · -- `0 < R ≤ 1`: `R^{-M} ≥ 1` and the left-hand side is at most `K₀`
    have hone : 1 ≤ (E.Kl * E.KL) ^ (-(E.intM : ℝ)) := by
      have h2 := Real.rpow_le_rpow_of_nonpos hR h1
        (neg_nonpos.mpr (Nat.cast_nonneg E.intM))
      rwa [Real.one_rpow] at h2
    calc ∑ s ∈ excited Mode, |E.hatChiSq s| * (1 - E.fL s)
        ≤ ∑ s ∈ excited Mode, |E.hatChiSq s| := by
          refine Finset.sum_le_sum fun s _ => ?_
          have h2 : 1 - E.fL s ≤ 1 := by linarith [h.fL_nonneg_holds s]
          calc |E.hatChiSq s| * (1 - E.fL s) ≤ |E.hatChiSq s| * 1 :=
                mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
            _ = |E.hatChiSq s| := by ring
      _ ≤ K₀ := h.sum_hatChiSq_le
      _ = K₀ * 1 := by ring
      _ ≤ K₀ * (E.Kl * E.KL) ^ (-(E.intM : ℝ)) :=
          mul_le_mul_of_nonneg_left hone (le_trans zero_le_one h.K₀_one)

/-! ## 3. The degenerate configurations `K_ℓK_L ≤ 0` -/

/-- **`f_L` vanishes on the excited modes when `K_ℓK_L ≤ 0`.**  The threshold
`K_L√(μa)` of `f_L` is `≤ 0` then, while `fL_supp` says `fLf p ≠ 0 → ‖p‖ ≤
K_L√(μa)`: if `K_L√(μa) < 0` this kills every `p`, and if it is `0` it kills every
`p ≠ 0` — and an excited mode has `kmom s ≠ 0` (`kmom_ne_holds`). -/
theorem fL_eq_zero_of_KL_nonpos (h : K15Input K₀ F T E) (hKL : E.KL ≤ 0)
    (s : Mode) (hs : s ∈ excited Mode) : E.fL s = 0 := by
  have hle : E.KL * Real.sqrt (E.mu * E.aScat) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hKL (Real.sqrt_nonneg _)
  by_contra hcon
  have h1 : h.fLf (h.kmom s) ≠ 0 := by rwa [← h.fL_eq s]
  have h2 : ‖h.kmom s‖ ≤ 0 := le_trans (h.fL_supp _ h1) hle
  have hkm : h.kmom s = 0 :=
    norm_eq_zero.mp (le_antisymm h2 (norm_nonneg _))
  exact h.kmom_ne_holds hs (by rw [h.kmom_eq s]; exact hkm)

/-- **The second conjunct in the degenerate configuration `K_ℓK_L ≤ 0`.**  By
`fL_eq_zero_of_KL_nonpos` its left-hand side is `∑_{s∈excited}|χ̂²_s|`: the
conjunct is *equivalent* to bounding that sum — a statement about the values
`χ̂²(2π·lift s)` of the localization function, not a consequence of `K15Input`. -/
theorem snd_conjunct_iff_of_KL_nonpos (h : K15Input K₀ F T E) (hKL : E.KL ≤ 0)
    (X : ℝ) :
    (∑ s ∈ excited Mode, |E.hatChiSq s| * (1 - E.fL s) ≤ X) ↔
      (∑ s ∈ excited Mode, |E.hatChiSq s| ≤ X) := by
  have hL : (∑ s ∈ excited Mode, |E.hatChiSq s| * (1 - E.fL s))
      = ∑ s ∈ excited Mode, |E.hatChiSq s| := by
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [h.fL_eq_zero_of_KL_nonpos hKL s hs]
    ring
  rw [hL]

/-- **The second conjunct at `K_ℓK_L = 0` with `M = E.intM ≥ 1`**: it is
*equivalent* to the sum of `|χ̂²|` over the modes being `0`, because
`(0:ℝ)^{-(M:ℝ)} = 0`.  This is the configuration that makes the delegated
statement unprovable. -/
theorem snd_conjunct_iff_sum_eq_zero_of_KL_eq_zero (h : K15Input K₀ F T E)
    (hKL : E.KL = 0) (hintM : 1 ≤ E.intM) :
    (∑ s ∈ excited Mode, |E.hatChiSq s| * (1 - E.fL s)
        ≤ K₀ * (E.Kl * E.KL) ^ (-(E.intM : ℝ))) ↔
      (∑ s ∈ excited Mode, |E.hatChiSq s| = 0) := by
  rw [h.snd_conjunct_iff_of_KL_nonpos (le_of_eq hKL)]
  have hpow : K₀ * (E.Kl * E.KL) ^ (-(E.intM : ℝ)) = 0 := by
    have hx : (-(E.intM : ℝ)) ≠ 0 := by
      rw [neg_ne_zero]
      exact_mod_cast (Nat.one_le_iff_ne_zero.mp hintM)
    rw [hKL, mul_zero, Real.zero_rpow hx, mul_zero]
  rw [hpow]
  constructor
  · intro hle
    exact le_antisymm hle (Finset.sum_nonneg fun s _ => abs_nonneg _)
  · intro hzero; rw [hzero]

end K15Input

/-! ## 4. The corrected statements -/

/-- **`chi_sums_of_decay` with the sharp side condition `0 < K_ℓK_L`.**  Both K2
fields of `Work.BoseB7A.Q3Kernel` (`sum_hatChiSq`, `tail_hatChiSq`), from the
`K15Input` lattice rows `sum_geom`/`sum_geom_tail` and the single `K₀`. -/
theorem chi_sums_of_decay_of_pos_KlKL (h : K15Input K₀ F T E)
    (hell : h.ell * E.KL * Real.sqrt (E.mu * E.aScat) = E.Kl * E.KL)
    (_hM : E.intM + 3 ≤ 2 * decayOrder)
    (hKL : 0 < E.Kl * E.KL) :
    (∑ s ∈ excited Mode, |E.hatChiSq s| ≤ K₀) ∧
    (∑ s ∈ excited Mode, |E.hatChiSq s| * (1 - E.fL s)
        ≤ K₀ * (E.Kl * E.KL) ^ (-(E.intM : ℝ))) :=
  ⟨h.sum_hatChiSq_le, h.tail_hatChiSq_le_of_pos hell hKL⟩

/-- **`chi_sums_of_decay` with FS's side condition `1 ≤ K_ℓK_L`** — the hypothesis
supplied at the call site (`Corpus.lean`) by `smallness_ratios`' ninth conjunct
(`1 ≤ E.Kl * E.KL`), and the form in which `count_PL_le` carries it. -/
theorem chi_sums_of_decay_of_one_le_KlKL (h : K15Input K₀ F T E)
    (hell : h.ell * E.KL * Real.sqrt (E.mu * E.aScat) = E.Kl * E.KL)
    (hM : E.intM + 3 ≤ 2 * decayOrder)
    (hKL : 1 ≤ E.Kl * E.KL) :
    (∑ s ∈ excited Mode, |E.hatChiSq s| ≤ K₀) ∧
    (∑ s ∈ excited Mode, |E.hatChiSq s| * (1 - E.fL s)
        ≤ K₀ * (E.Kl * E.KL) ^ (-(E.intM : ℝ))) :=
  chi_sums_of_decay_of_pos_KlKL h hell hM (lt_of_lt_of_le one_pos hKL)

/-! ## 5. The delegated statement (reproduced verbatim) -/

/-- **The corrected statement.**  The unfixed form above (with `hM` and no
`hKL`) is refuted in the header; with FS's side condition `1 ≤ K_ℓK_L` (S10 of
§10's smallness list, `con:KellKL`) the two conjuncts hold.  This is the form
`Work.BoseK15.Corpus` consumes. -/
theorem chi_sums_of_decay_fixed_statement (h : K15Input K₀ F T E)
    (hell : h.ell * E.KL * Real.sqrt (E.mu * E.aScat) = E.Kl * E.KL)
    (hKL : 1 ≤ E.Kl * E.KL)
    (hM : E.intM + 3 ≤ 2 * decayOrder) :
    (∑ s ∈ excited Mode, |E.hatChiSq s| ≤ K₀) ∧
    (∑ s ∈ excited Mode, |E.hatChiSq s| * (1 - E.fL s)
        ≤ K₀ * (E.Kl * E.KL) ^ (-(E.intM : ℝ))) :=
  chi_sums_of_decay_of_one_le_KlKL h hell hM hKL

end Work.BoseK15
