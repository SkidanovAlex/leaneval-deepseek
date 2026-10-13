import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.OpenPkg.radialMul_field
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows.NRow10aux

set_option maxHeartbeats 1600000

/-!
## The pointwise majorant `HkIntegrand α 4 (r · g) ≤ K · HkIntegrand α 4 g` for radial `r`

`r` is a radial coefficient all of whose `D_z`-iterates up to order `4` are bounded by `1`
on `z ≥ 0` (this is exactly the hypothesis available for the radial factors of the
nonlinearity in the `NRow` estimates); `g` is arbitrary.  The claim is that the full `ℋ⁴`
integrand of the product `r · g` is pointwise dominated by a universal multiple of that of
`g` — in particular the constant does **not** depend on `α`.

The proof is the binomial expansion of `D_z^i (r·g)` resp. `D_z^j D_θ^i (r·g)`
(`Work.FTS.OpenPkg.leibniz_rad_Dz`, `Work.FTS.OpenPkg.leibniz_rad_mixed`; all angular
derivatives fall on `g` because `r` is radial), Cauchy–Schwarz on the resulting finite sums
(`sq_sum_le_card_mul_sum_sq`) together with `i.choose b ≤ 2^i ≤ 16`, and the fact that each
Leibniz summand is a genuine summand of `HkIntegrand α 4 g` (`sq_le_HkIntegrand_z`,
`sq_le_HkIntegrand_mixed`).

Unlike the sibling `starProdPt` (which needs `0 < α ≤ 1` to trade a surplus power of
`sin 2θ` against the angular weight `Wt`), the radial case needs **no** comparison between
the `η`-weight `w/ sin(2θ)^{η/2}` and the `γ`-weight `Wt α`: the slots of `r·g` have exactly
the same weights as those of `g`, so the estimate holds for every real `α`.
-/

/-- `i.choose b ≤ 2^i ≤ 16` for `i ≤ 4`, hence `(i.choose b)² ≤ 256`. -/
private theorem choose_sq_le_256 (i b : ℕ) (_hb : b ≤ i) (hi : i ≤ 4) :
    ((i.choose b : ℕ) : ℝ) ^ 2 ≤ 256 := by
  have h1 : i.choose b ≤ 2 ^ i := Nat.choose_le_two_pow i b
  have h2 : 2 ^ i ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hi
  have h3 : ((i.choose b : ℕ) : ℝ) ≤ 16 := by
    have h : i.choose b ≤ 16 := by omega
    exact_mod_cast h
  nlinarith [h3, Nat.cast_nonneg (α := ℝ) (i.choose b)]

/-- A single pure `D_z`-slot of the `ℋ⁴`-integrand of the radial product `r · g`. -/
private theorem zslot_bound {α : ℝ} {r : ℝ → ℝ} {g : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hr : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => r z))
    (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hR : ∀ b : ℕ, b ≤ 4 → |Work.Elliptic.DzdIter b r z| ≤ 1)
    (i : ℕ) (hi : i ≤ 4) :
    (Work.Spaces.DzIter i (fun z θ => r z * g z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ 6400 * Work.Spaces.HkIntegrand α 4 g z θ := by
  have hHk : 0 ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
    Work.Spaces.HkIntegrand_nonneg α 4 g z θ
  have hlei := Work.FTS.OpenPkg.leibniz_rad_Dz r g hr hg i z (Set.mem_Ioi.mpr hz) θ
    (Set.mem_Ioo.mpr ⟨hθ0, hθ1⟩)
  have hsum : Work.Spaces.DzIter i (fun z θ => r z * g z θ) z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      = ∑ b ∈ Finset.range (i + 1),
          (((i.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b r z
            * (Work.Spaces.DzIter (i - b) g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) := by
    rw [hlei, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [hsum]
  have hper : ∀ b ∈ Finset.range (i + 1),
      ((((i.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b r z
            * (Work.Spaces.DzIter (i - b) g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2)
      ≤ 256 * Work.Spaces.HkIntegrand α 4 g z θ := by
    intro b hbmem
    have hbi : b ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp hbmem)
    have hchoose : (((i.choose b : ℕ) : ℝ)) ^ 2 ≤ 256 := choose_sq_le_256 i b hbi hi
    have hRd : (Work.Elliptic.DzdIter b r z) ^ 2 ≤ 1 := by
      have hx := hR b (by omega)
      rw [← sq_abs]
      nlinarith [hx, abs_nonneg (Work.Elliptic.DzdIter b r z)]
    have hG : (Work.Spaces.DzIter (i - b) g z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
      Work.Spaces.sq_le_HkIntegrand_z α 4 g z θ (i - b) (by omega)
    calc ((((i.choose b : ℕ) : ℝ)) * (Work.Elliptic.DzdIter b r z
            * (Work.Spaces.DzIter (i - b) g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2
        = (((i.choose b : ℕ) : ℝ)) ^ 2 * (Work.Elliptic.DzdIter b r z) ^ 2
            * (Work.Spaces.DzIter (i - b) g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by ring
      _ ≤ 256 * 1 * Work.Spaces.HkIntegrand α 4 g z θ :=
          mul_le_mul (mul_le_mul hchoose hRd (sq_nonneg _) (by norm_num)) hG
            (sq_nonneg _) (by norm_num)
      _ = 256 * Work.Spaces.HkIntegrand α 4 g z θ := by ring
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (i + 1))
    (f := fun b => (((i.choose b : ℕ) : ℝ)) * (Work.Elliptic.DzdIter b r z
            * (Work.Spaces.DzIter (i - b) g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))))
  have hcard : (((Finset.range (i + 1)).card : ℕ) : ℝ) ≤ 5 := by
    rw [Finset.card_range]
    exact_mod_cast (by omega : i + 1 ≤ 5)
  have hsum2 : (∑ b ∈ Finset.range (i + 1),
        ((((i.choose b : ℕ) : ℝ)) * (Work.Elliptic.DzdIter b r z
            * (Work.Spaces.DzIter (i - b) g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2)
      ≤ 5 * (256 * Work.Spaces.HkIntegrand α 4 g z θ) := by
    calc (∑ b ∈ Finset.range (i + 1),
          ((((i.choose b : ℕ) : ℝ)) * (Work.Elliptic.DzdIter b r z
              * (Work.Spaces.DzIter (i - b) g z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2)
        ≤ ∑ _b ∈ Finset.range (i + 1), (256 * Work.Spaces.HkIntegrand α 4 g z θ) :=
          Finset.sum_le_sum hper
      _ = ((i + 1 : ℕ) : ℝ) * (256 * Work.Spaces.HkIntegrand α 4 g z θ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ 5 * (256 * Work.Spaces.HkIntegrand α 4 g z θ) := by
          refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (by norm_num) hHk)
          exact_mod_cast (by omega : i + 1 ≤ 5)
  refine hcs.trans ?_
  calc (((Finset.range (i + 1)).card : ℕ) : ℝ)
          * ∑ b ∈ Finset.range (i + 1),
              ((((i.choose b : ℕ) : ℝ)) * (Work.Elliptic.DzdIter b r z
                * (Work.Spaces.DzIter (i - b) g z θ
                  * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))))) ^ 2
      ≤ 5 * (5 * (256 * Work.Spaces.HkIntegrand α 4 g z θ)) :=
        mul_le_mul hcard hsum2 (Finset.sum_nonneg fun b _ => sq_nonneg _) (by norm_num)
    _ = 6400 * Work.Spaces.HkIntegrand α 4 g z θ := by ring

/-- A single mixed slot (`1 ≤ i`) of the `ℋ⁴`-integrand of the radial product `r · g`. -/
private theorem mslot_bound {α : ℝ} {r : ℝ → ℝ} {g : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hr : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => r z))
    (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hR : ∀ b : ℕ, b ≤ 4 → |Work.Elliptic.DzdIter b r z| ≤ 1)
    (i j : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) :
    (Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ 6400 * Work.Spaces.HkIntegrand α 4 g z θ := by
  have hHk : 0 ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
    Work.Spaces.HkIntegrand_nonneg α 4 g z θ
  have hj4 : j ≤ 4 := by omega
  have hlei := Work.FTS.OpenPkg.leibniz_rad_mixed r g hr hg j i hi z (Set.mem_Ioi.mpr hz) θ
    (Set.mem_Ioo.mpr ⟨hθ0, hθ1⟩)
  have hsum : Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ * Work.Spaces.Wt α z θ
      = ∑ b ∈ Finset.range (j + 1),
          (((j.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b r z
            * (Work.Spaces.mixed (j - b) i g z θ * Work.Spaces.Wt α z θ))) := by
    rw [hlei, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [hsum]
  have hper : ∀ b ∈ Finset.range (j + 1),
      ((((j.choose b : ℕ) : ℝ) * (Work.Elliptic.DzdIter b r z
            * (Work.Spaces.mixed (j - b) i g z θ * Work.Spaces.Wt α z θ))) ^ 2)
      ≤ 256 * Work.Spaces.HkIntegrand α 4 g z θ := by
    intro b hbmem
    have hbj : b ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hbmem)
    have hchoose : (((j.choose b : ℕ) : ℝ)) ^ 2 ≤ 256 := choose_sq_le_256 j b hbj hj4
    have hRd : (Work.Elliptic.DzdIter b r z) ^ 2 ≤ 1 := by
      have hx := hR b (by omega)
      rw [← sq_abs]
      nlinarith [hx, abs_nonneg (Work.Elliptic.DzdIter b r z)]
    have hG : (Work.Spaces.mixed (j - b) i g z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
      Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ i (j - b) hi (by omega)
    calc ((((j.choose b : ℕ) : ℝ)) * (Work.Elliptic.DzdIter b r z
            * (Work.Spaces.mixed (j - b) i g z θ * Work.Spaces.Wt α z θ))) ^ 2
        = (((j.choose b : ℕ) : ℝ)) ^ 2 * (Work.Elliptic.DzdIter b r z) ^ 2
            * (Work.Spaces.mixed (j - b) i g z θ * Work.Spaces.Wt α z θ) ^ 2 := by ring
      _ ≤ 256 * 1 * Work.Spaces.HkIntegrand α 4 g z θ :=
          mul_le_mul (mul_le_mul hchoose hRd (sq_nonneg _) (by norm_num)) hG
            (sq_nonneg _) (by norm_num)
      _ = 256 * Work.Spaces.HkIntegrand α 4 g z θ := by ring
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (j + 1))
    (f := fun b => (((j.choose b : ℕ) : ℝ)) * (Work.Elliptic.DzdIter b r z
            * (Work.Spaces.mixed (j - b) i g z θ * Work.Spaces.Wt α z θ)))
  have hcard : (((Finset.range (j + 1)).card : ℕ) : ℝ) ≤ 5 := by
    rw [Finset.card_range]
    exact_mod_cast (by omega : j + 1 ≤ 5)
  have hsum2 : (∑ b ∈ Finset.range (j + 1),
        ((((j.choose b : ℕ) : ℝ)) * (Work.Elliptic.DzdIter b r z
            * (Work.Spaces.mixed (j - b) i g z θ * Work.Spaces.Wt α z θ))) ^ 2)
      ≤ 5 * (256 * Work.Spaces.HkIntegrand α 4 g z θ) := by
    calc (∑ b ∈ Finset.range (j + 1),
          ((((j.choose b : ℕ) : ℝ)) * (Work.Elliptic.DzdIter b r z
              * (Work.Spaces.mixed (j - b) i g z θ * Work.Spaces.Wt α z θ))) ^ 2)
        ≤ ∑ _b ∈ Finset.range (j + 1), (256 * Work.Spaces.HkIntegrand α 4 g z θ) :=
          Finset.sum_le_sum hper
      _ = ((j + 1 : ℕ) : ℝ) * (256 * Work.Spaces.HkIntegrand α 4 g z θ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ 5 * (256 * Work.Spaces.HkIntegrand α 4 g z θ) := by
          refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (by norm_num) hHk)
          exact_mod_cast (by omega : j + 1 ≤ 5)
  refine hcs.trans ?_
  calc (((Finset.range (j + 1)).card : ℕ) : ℝ)
          * ∑ b ∈ Finset.range (j + 1),
              ((((j.choose b : ℕ) : ℝ)) * (Work.Elliptic.DzdIter b r z
                * (Work.Spaces.mixed (j - b) i g z θ * Work.Spaces.Wt α z θ))) ^ 2
      ≤ 5 * (5 * (256 * Work.Spaces.HkIntegrand α 4 g z θ)) :=
        mul_le_mul hcard hsum2 (Finset.sum_nonneg fun b _ => sq_nonneg _) (by norm_num)
    _ = 6400 * Work.Spaces.HkIntegrand α 4 g z θ := by ring

theorem radialBounded_majorant :
    ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ) (r : ℝ → ℝ) (g : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => r z) →
      Work.FTS.EllipticEst.SmoothOpen g →
      (∀ b : ℕ, b ≤ 4 → ∀ z : ℝ, 0 ≤ z → |Work.Elliptic.DzdIter b r z| ≤ 1) →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        Work.Spaces.HkIntegrand α 4 (fun z θ => r z * g z θ) z θ
          ≤ K * Work.Spaces.HkIntegrand α 4 g z θ := by
  refine ⟨200000, by norm_num, ?_⟩
  intro α r g hr hg hbnd z θ hz hθ0 hθ1
  have hHk : 0 ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
    Work.Spaces.HkIntegrand_nonneg α 4 g z θ
  have hR : ∀ b : ℕ, b ≤ 4 → |Work.Elliptic.DzdIter b r z| ≤ 1 :=
    fun b hb => hbnd b hb z (le_of_lt hz)
  conv_lhs => rw [Work.Spaces.HkIntegrand]
  have hA : (∑ i ∈ Finset.range (4 + 1), (Work.Spaces.DzIter i
        (fun z θ => r z * g z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ 5 * (6400 * Work.Spaces.HkIntegrand α 4 g z θ) := by
    calc (∑ i ∈ Finset.range (4 + 1), (Work.Spaces.DzIter i
          (fun z θ => r z * g z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ ∑ _i ∈ Finset.range (4 + 1), (6400 * Work.Spaces.HkIntegrand α 4 g z θ) :=
          Finset.sum_le_sum fun i hi =>
            zslot_bound hr hg hz hθ0 hθ1 hR i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
      _ = 5 * (6400 * Work.Spaces.HkIntegrand α 4 g z θ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          norm_num
  have hB : (∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
        (if 1 ≤ i ∧ i + j ≤ 4 then
          (Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0))
      ≤ 25 * (6400 * Work.Spaces.HkIntegrand α 4 g z θ) := by
    calc (∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
          (if 1 ≤ i ∧ i + j ≤ 4 then
            (Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ
              * Work.Spaces.Wt α z θ) ^ 2 else 0))
        ≤ ∑ _i ∈ Finset.range (4 + 1), ∑ _j ∈ Finset.range (4 + 1),
            (6400 * Work.Spaces.HkIntegrand α 4 g z θ) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          by_cases hc : 1 ≤ i ∧ i + j ≤ 4
          · rw [if_pos hc]
            exact mslot_bound hr hg hz hθ0 hθ1 hR i j hc.1 hc.2
          · rw [if_neg hc]
            exact mul_nonneg (by norm_num) hHk
      _ = 25 * (6400 * Work.Spaces.HkIntegrand α 4 g z θ) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  linarith [hA, hB, hHk]

end Work.FTS.NonlinRows.NRow10aux
