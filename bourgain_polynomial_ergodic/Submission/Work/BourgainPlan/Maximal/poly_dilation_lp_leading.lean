import Mathlib
import Submission.Work.BourgainPlan.Maximal.poly_dilation_lp

namespace Work.BourgainPlan.Maximal

open MeasureTheory Set Finset
open scoped ENNReal

/-! ## Reduction of Bourgain (7.17) to the nonnegative case

The proof of `poly_dilation_lp` needs `q = P.map (Int.castRingHom ℝ)` to be nonnegative on
`[0,∞)`.  If only `0 < P.leadingCoeff` is assumed then `q` is bounded below on `[0,∞)`
(`q.eval u → +∞` because the leading coefficient is positive, and `q` is continuous on the
compact piece `[0,K]`); hence some *integer* shift `m` makes `q + m` nonnegative there.  If the
shifted polynomial `P + C m` satisfies the estimate of `poly_dilation_lp` with constant `C`,
then so does `P`, because `q.eval u + m` is compensated by translating the test function:
with `ψ'(y) = ψ (y + m)` we have `ψ' (x - (q.eval u + m)) = ψ (x - q.eval u)` pointwise, while
`∫ (ψ' y)^p dy = ∫ (ψ y)^p dy` by translation invariance of Lebesgue measure. -/

/-- Adding the constant polynomial `C m` to `P` shifts the values of the mapped real polynomial
by `(m : ℝ)`. -/
lemma poly_eval_map_add_C (P : Polynomial ℤ) (m : ℤ) (u : ℝ) :
    ((P + Polynomial.C m).map (Int.castRingHom ℝ)).eval u
      = (P.map (Int.castRingHom ℝ)).eval u + (m : ℝ) := by
  rw [Polynomial.map_add, Polynomial.map_C, Polynomial.eval_add, Polynomial.eval_C]
  norm_num

/-- A polynomial with positive leading coefficient is bounded below on `[0,∞)`: some integer
shift makes it nonnegative there. -/
lemma poly_leading_shift_nonneg (P : Polynomial ℤ) (hP : 0 < P.leadingCoeff) :
    ∃ m : ℤ, ∀ x : ℝ, 0 ≤ x → 0 ≤ (P.map (Int.castRingHom ℝ)).eval x + (m : ℝ) := by
  set q : Polynomial ℝ := P.map (Int.castRingHom ℝ) with hq
  have hlead : 0 < q.leadingCoeff := by
    rw [hq, Polynomial.leadingCoeff_map_of_injective (RingHom.injective_int (Int.castRingHom ℝ))]
    exact Int.cast_pos.mpr hP
  -- `q` is eventually positive, being asymptotically `leadingCoeff * u ^ natDegree`
  have hg : ∀ᶠ x : ℝ in Filter.atTop, 0 < q.leadingCoeff * x ^ q.natDegree := by
    filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with x hx
    exact mul_pos hlead (pow_pos hx _)
  have hpos : ∀ᶠ x : ℝ in Filter.atTop, 0 < q.eval x :=
    (Polynomial.isEquivalent_atTop_lead q).eventually_pos hg
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 hpos
  -- on the compact piece `[0, max K 0]` the polynomial attains a minimum
  obtain ⟨x₀, _hx₀mem, hx₀min⟩ := isCompact_Icc.exists_isMinOn
    (Set.nonempty_Icc.mpr (le_max_right K 0)) (Polynomial.continuous q).continuousOn
  -- the integer `⌈-min (q x₀) 0⌉` is large enough
  refine ⟨Int.ceil (-(min (q.eval x₀) 0)), fun x hx => ?_⟩
  have hb : min (q.eval x₀) 0 ≤ q.eval x := by
    rcases lt_or_ge x (max K 0) with hxK | hxK
    · exact le_trans (min_le_left _ _) (hx₀min ⟨hx, hxK.le⟩)
    · exact le_trans (min_le_right _ _) (le_of_lt (hK x (le_trans (le_max_left K 0) hxK)))
  have hceil : -(min (q.eval x₀) 0) ≤ ((⌈-(min (q.eval x₀) 0)⌉ : ℤ) : ℝ) := Int.le_ceil _
  linarith

/-- **Bourgain (7.17) with the hypothesis weakened to a positive leading coefficient.**

`Work.BourgainPlan.Maximal.poly_dilation_lp` (`poly_dilation_lp.lean`, PROVED) proves this for
polynomials nonnegative on all of `[0,∞)`.  The statement here requires only `0 < P.leadingCoeff`
and `1 ≤ P.natDegree`, which is what the target's hypotheses give: for `P` nonnegative on `ℕ` with
`2 ≤ P.natDegree` one has `0 < P.leadingCoeff`
(`Work.BourgainPlan.Maximal.leadingCoeff_pos_of_nonnegOnNat`, `kernel_l2.lean`), and degree `1` is
covered separately by `deg_le_one`.  `P = X² − X` (nonnegative on `ℕ`, negative on `(0,1)`,
`leadingCoeff = 1`) satisfies the hypotheses here but not those of `poly_dilation_lp`.

Reviewers' route: the existing proof consumes nonnegativity in exactly three places, and each
survives under `0 < P.leadingCoeff` after enlarging the cut-off `U` — (i) `0 < leadingCoeff` (now a
hypothesis), (ii) the asymptotic derivative bound `c·u^{d−1} ≤ q'` and `q ≤ C₀·u^d` for large `u`
(pure asymptotics), and (iii) `0 ≤ q` on `[U,∞)` (eventual, since `q → +∞`); the finite region
`(0,U]` is covered by the finitely many monotone pieces of `exists_cover_deriv_ne` as before, and
negative values of `P` live on a bounded set, where the shifts are bounded translations handled by
`hlMax`/`tail_le_hlMax`.  Concretely this needs a variant of `poly_growth` taking
`0 < P.leadingCoeff` and a re-instantiation of `tail_le_hlMax` — not a one-line hypothesis swap. -/
theorem poly_dilation_lp_leading (P : Polynomial ℤ) (hP : 0 < P.leadingCoeff) (hd : 1 ≤ P.natDegree)
    {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ψ : ℝ → ℝ≥0∞), Measurable ψ → (∀ x, ψ x ≠ ⊤) →
      (MeasureTheory.lintegral MeasureTheory.volume (fun x => ENNReal.rpow (ψ x) p) < ⊤) →
      MeasureTheory.lintegral MeasureTheory.volume
          (fun x => ENNReal.rpow (iSup fun N : ℕ =>
            MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) 1))
              (fun s => ψ (x - (P.map (Int.castRingHom ℝ)).eval ((N : ℝ) * s)))) p)
        ≤ ENNReal.ofReal C *
          MeasureTheory.lintegral MeasureTheory.volume (fun x => ENNReal.rpow (ψ x) p) := by
  -- shift `P` by an integer constant until it is nonnegative on `[0,∞)`
  -- the hypothesis `hd : 1 ≤ P.natDegree` is not needed below: the shift argument also
  -- covers the constant case (where no shift is necessary)
  have _hd := hd
  obtain ⟨m, hm⟩ := poly_leading_shift_nonneg P hP
  have hQ : ∀ x : ℝ, 0 ≤ x → 0 ≤ ((P + Polynomial.C m).map (Int.castRingHom ℝ)).eval x := by
    intro x hx
    rw [poly_eval_map_add_C]
    exact hm x hx
  obtain ⟨C, hC, hbound⟩ :=
    poly_dilation_lp (P + Polynomial.C m) hQ hp
  refine ⟨C, hC, fun ψ hψ hψfin hH => ?_⟩
  show ((∫⁻ x, (⨆ N : ℕ, ∫⁻ s in Set.Ioc (0:ℝ) 1,
      ψ (x - (P.map (Int.castRingHom ℝ)).eval ((N:ℝ)*s))) ^ p))
    ≤ ENNReal.ofReal C * (∫⁻ x, (ψ x) ^ p)
  -- compensate the shift by translating the test function
  set ψ' : ℝ → ℝ≥0∞ := fun y => ψ (y + (m:ℝ)) with hψ'def
  have hψ'meas : Measurable ψ' := hψ.comp (measurable_id.add measurable_const)
  have hψ'fin : ∀ y, ψ' y ≠ ⊤ := fun y => hψfin _
  have hRHS : (∫⁻ y, (ψ' y) ^ p) = ∫⁻ y, (ψ y) ^ p := by
    rw [hψ'def]
    exact MeasureTheory.lintegral_add_right_eq_self (fun y => (ψ y) ^ p) (m:ℝ)
  have hH' : ∫⁻ y, (ψ' y) ^ p < ⊤ := by rw [hRHS]; exact hH
  have hkey := hbound ψ' hψ'meas hψ'fin hH'
  -- the shifted maximal operator applied to `ψ'` is *pointwise* the original one applied to `ψ`
  have hLHS : (∫⁻ x, (⨆ N : ℕ, ∫⁻ s in Set.Ioc (0:ℝ) 1,
      ψ (x - (P.map (Int.castRingHom ℝ)).eval ((N:ℝ)*s))) ^ p)
      = (∫⁻ x, (⨆ N : ℕ, ∫⁻ s in Set.Ioc (0:ℝ) 1,
      ψ' (x - ((P + Polynomial.C m).map (Int.castRingHom ℝ)).eval ((N:ℝ)*s))) ^ p) := by
    refine lintegral_congr fun x => ?_
    have h1 : (⨆ N : ℕ, ∫⁻ s in Set.Ioc (0:ℝ) 1,
        ψ (x - (P.map (Int.castRingHom ℝ)).eval ((N:ℝ)*s)))
      = (⨆ N : ℕ, ∫⁻ s in Set.Ioc (0:ℝ) 1,
        ψ' (x - ((P + Polynomial.C m).map (Int.castRingHom ℝ)).eval ((N:ℝ)*s))) := by
      refine iSup_congr fun N => ?_
      refine lintegral_congr fun s => ?_
      rw [hψ'def, poly_eval_map_add_C]
      congr 1
      ring
    rw [h1]
  calc (∫⁻ x, (⨆ N : ℕ, ∫⁻ s in Set.Ioc (0:ℝ) 1,
        ψ (x - (P.map (Int.castRingHom ℝ)).eval ((N:ℝ)*s))) ^ p)
      = (∫⁻ x, (⨆ N : ℕ, ∫⁻ s in Set.Ioc (0:ℝ) 1,
        ψ' (x - ((P + Polynomial.C m).map (Int.castRingHom ℝ)).eval ((N:ℝ)*s))) ^ p) := hLHS
    _ ≤ ENNReal.ofReal C * (∫⁻ y, (ψ' y) ^ p) := hkey
    _ = ENNReal.ofReal C * (∫⁻ y, (ψ y) ^ p) := by rw [hRHS]

end Work.BourgainPlan.Maximal
