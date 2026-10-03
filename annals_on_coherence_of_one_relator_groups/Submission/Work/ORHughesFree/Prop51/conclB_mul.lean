import Mathlib
import Submission.Work.ORHughesFree.Prop51.ConclB
import Submission.Work.ORHughesFree.Prop51.conj
import Submission.Work.ORHughesFree.Tree.exp_mono
import Submission.Work.ORHughesFree.SkewLaurentSeries.mul_apply_eq_single
import Submission.Work.ORHughesFree.SkewLaurentSeries.mul_apply_eq_single_right
import Submission.Work.ORHughesFree.Tree.olt_dlog_of_lt_exp
import Submission.Work.ORHughesFree.Tree.olt_dlog_sum
import Submission.Work.ORHughesFree.Prop51.treeH_coeffToP_mul_ofAdd_le
import Submission.Work.ORHughesFree.Prop51.olt_dlog_coeffToP_mul_ofAdd

set_option autoImplicit false

namespace Work.ORHughesFree.Prop51

open Work.ORHughesFree

/-- Product step of [JZLA20, Proposition 5.1]: with bounds `T₁`, `T₂` of *width one*
(`Tree.wid T₁ = Tree.wid T₂ = 1`, the case when `x` and `y` are images of words of `ℛ(U)`).

Sketch. Write `x = laurentEmbed f`, `y = laurentEmbed g` using `hx`, `hy` and take `F = f * g` as
the witness for `x * y`: `laurentEmbed F = x * y` because `laurentEmbed` is a ring homomorphism.
By `SkewLaurentSeries.mul_apply` (better `mul_apply_of_bounds`) the `n`-th coefficient of `F` is
`∑ i ∈ Icc (lo f) (n - lo g), f.1 i * (ofAdd i • g.1 (n - i))`, and by
`Work.ORHughesFree.Prop51.conj` applied to the coefficients its image in `P` is
`∑ i, coeffToP (f.1 i) * Φ(ofGroup (t^i)) * coeffToP (g.1 (n-i)) * Φ(ofGroup (t^{-i}))`.
(`treeH_conj_eq` in `ConclB.lean` says conjugation by `Φ(ofGroup (t^i))` preserves `treeH`, and
`treeH_ofGroup` that this factor has complexity `1`.)

Let `A`, `B` be the trees with `Tree.log T₁ = some A`, `Tree.log T₂ = some B` (they exist as
`T₁, T₂ ≠ 0`), so that `Tree.log (T₁*T₂) = some (A+B)` (`Tree.log_mul`) and `dlog (T₁*T₂) =
oadd (dlog T₁) (dlog T₂)`.  The coefficient bounds from `hx`, `hy` give, by monotonicity of `dlog`
(`Tree.ole_dlog_of_le`), `Tree.Ole (dlog (treeH cᵢ)) (some A)` for every coefficient `cᵢ` of `x`,
and similarly `some B` for `y`; hence `Tree.Ole (dlog (treeH (F.1 n))) (some (A+B))` for every `n`
using `Tree.ole_dlog_mul`, `Tree.ole_dlog_add`, `Tree.ole_omax_of`/`Tree.ole_listOMax` and
`Tree.olt_oadd_some`, the last one in the form: if some coefficient of `x` fails to have
`dlog (treeH cᵢ) = some A` or some coefficient of `y` fails to have `dlog (treeH dⱼ) = some B`,
then `Tree.Olt (dlog (treeH (F.1 n))) (some (A+B))`, whence `Tree.lt (treeH (F.1 n)) (T₁*T₂)` by
`Tree.lt_of_olt_dlog` (since `dlog (T₁*T₂) = some (A+B)`).

Dichotomy, per index `n`:
* if `Tree.Olt (dlog (treeH (F.1 n))) (dlog (T₁*T₂))` then `treeH (F.1 n) < T₁*T₂` and the
  `"= T₁*T₂"` case of the third clause is vacuous;
* if `Tree.Ole (dlog (T₁*T₂)) (dlog (treeH (F.1 n)))` (forced by the estimate and totality,
  `Tree.ole_total`), the equality of options, together with the finite-max argument above, produces
  an index `i` with `dlog (treeH (coeffToP (f.1 i))) = some A` and
  `dlog (treeH (coeffToP (g.1 (n-i)))) = some B`.  Since `Tree.wid T₁ = 1` and
  `Tree.log T₁ = some A`, `Tree.eq_exp_log_of_wid_eq_one` gives `T₁ = Tree.exp A`; with
  `Tree.le_exp_log` (`exp A ≤ c`) and `c ≤ T₁` this upgrades to `treeH (coeffToP (f.1 i)) = T₁`, so
  the *third clause* of `hx` gives `f.1 j = 0` for all `j ≠ i`; symmetrically `g.1 j = 0` for all
  `j ≠ n - i`.  Hence `F` is a monomial (`SkewLaurentSeries.mono_mul`/`mono_mul_apply`, or directly
  `SkewLaurentSeries.ext`: `F.1 j = f.1 i * (ofAdd i • g.1 (j-i))`), so the third clause of the
  goal holds, and the bound at the single index follows from `treeH_le_mul`, `treeH_conj_eq` and
  the coefficient bounds `treeH (coeffToP (f.1 i)) ≤ T₁`, `treeH (coeffToP (g.1 (n-i))) ≤ T₂`. -/
theorem conclB_mul {Γ : Type} [Group Γ] {P : Type} [Ring P] {DN : Subring P}
    [MulSemiringAction (Multiplicative ℤ) ↥DN] (d : Work.ORHughesFree.Prop51Data Γ P DN)
    {x y : P} {T₁ T₂ : Work.ORHughesFree.Tree}
    (hx : Work.ORHughesFree.Prop51.ConclB d x T₁) (hy : Work.ORHughesFree.Prop51.ConclB d y T₂)
    (hT₁ : T₁ ≠ 0) (hT₂ : T₂ ≠ 0)
    (hw₁ : Work.ORHughesFree.Tree.wid T₁ = 1) (hw₂ : Work.ORHughesFree.Tree.wid T₂ = 1) :
    Work.ORHughesFree.Prop51.ConclB d (x * y) (T₁ * T₂) := by
  obtain ⟨f, hf, hfb, hfm⟩ := hx
  obtain ⟨g, hg, hgb, hgm⟩ := hy
  -- `T₁` and `T₂` have width one, so they are single root extensions `exp A` and `exp B`.
  obtain ⟨A, hA⟩ := (Tree.log_spec T₁).2.2 hT₁
  obtain ⟨B, hB⟩ := (Tree.log_spec T₂).2.2 hT₂
  have hT₁e : T₁ = Tree.exp A := Tree.eq_exp_log_of_wid_eq_one hA hw₁
  have hT₂e : T₂ = Tree.exp B := Tree.eq_exp_log_of_wid_eq_one hB hw₂
  have hAB : Tree.dlog (T₁ * T₂) = some (A + B) := Tree.log_mul hA hB
  have hne : T₁ * T₂ ≠ 0 := by
    rw [hT₁e, hT₂e, ← Tree.exp_add]
    exact Tree.exp_ne_zero (A + B)
  have hFG : d.laurentEmbed (f * g) = x * y := by rw [map_mul, hf, hg]
  by_cases hfmax : ∃ i : ℤ, d.treeH (d.coeffToP (f.1 i)) = T₁
  · by_cases hgmax : ∃ j : ℤ, d.treeH (d.coeffToP (g.1 j)) = T₂
    · -- both `x` and `y` have a coefficient of complexity `T₁` resp. `T₂`, so both are monomials
      obtain ⟨i₀, hi₀⟩ := hfmax
      obtain ⟨j₀, hj₀⟩ := hgmax
      have hfmono : ∀ j : ℤ, j ≠ i₀ → f.1 j = 0 := fun j hj => hfm i₀ hi₀ j hj
      have hgmono : ∀ j : ℤ, j ≠ j₀ → g.1 j = 0 := fun j hj => hgm j₀ hj₀ j hj
      refine ⟨f * g, hFG, fun n => ?_, fun n hn j hj => ?_⟩
      · rw [SkewLaurentSeries.mul_apply_eq_single f g i₀ n hfmono]
        refine Tree.le_trans (treeH_coeffToP_mul_ofAdd_le d f g n i₀) ?_
        rw [hi₀]
        exact Tree.le_mul (Tree.le_refl T₁) (hgb (n - i₀))
      · rw [SkewLaurentSeries.mul_apply_eq_single f g i₀ j hfmono]
        have hjne : j - i₀ ≠ j₀ := by
          intro hji
          have hnne : n - i₀ ≠ j₀ := by
            intro hni
            have hnj : n = j := by omega
            exact hj hnj.symm
          have hz : (f * g).1 n = 0 := by
            rw [SkewLaurentSeries.mul_apply_eq_single f g i₀ n hfmono,
              hgmono (n - i₀) hnne, smul_zero, mul_zero]
          have hzT : d.treeH (d.coeffToP ((f * g).1 n)) = 0 := by
            rw [hz]
            exact treeH_zero d
          rw [hzT] at hn
          exact hne hn.symm
        rw [hgmono (j - i₀) hjne, smul_zero, mul_zero]
    · -- `x` is a monomial, but no coefficient of `y` has complexity `T₂`; all coefficients of
      -- `y` are then *strictly* below `T₂` and the bound is strict for every index
      obtain ⟨i₀, hi₀⟩ := hfmax
      have hfmono : ∀ j : ℤ, j ≠ i₀ → f.1 j = 0 := fun j hj => hfm i₀ hi₀ j hj
      have hg_lt : ∀ j : ℤ, Tree.lt (d.treeH (d.coeffToP (g.1 j))) T₂ :=
        fun j => Tree.lt_of_le_of_ne (hgb j) (fun h => hgmax ⟨j, h⟩)
      have hlt : ∀ n : ℤ, Tree.lt (d.treeH (d.coeffToP ((f * g).1 n))) (T₁ * T₂) := by
        intro n
        rw [SkewLaurentSeries.mul_apply_eq_single f g i₀ n hfmono]
        refine Tree.lt_of_le_of_lt' (treeH_coeffToP_mul_ofAdd_le d f g n i₀) ?_
        rw [hi₀]
        exact Tree.lt_mul_left (hg_lt (n - i₀)) hT₁
      refine ⟨f * g, hFG, fun n => Tree.le_of_lt (hlt n), fun n hn j hj => ?_⟩
      exact absurd (hn ▸ hlt n) Tree.lt_irrefl
  · by_cases hgmax : ∃ j : ℤ, d.treeH (d.coeffToP (g.1 j)) = T₂
    · -- symmetric case: `y` is a monomial, all coefficients of `x` are strictly below `T₁`
      obtain ⟨j₀, hj₀⟩ := hgmax
      have hgmono : ∀ j : ℤ, j ≠ j₀ → g.1 j = 0 := fun j hj => hgm j₀ hj₀ j hj
      have hf_lt : ∀ i : ℤ, Tree.lt (d.treeH (d.coeffToP (f.1 i))) T₁ :=
        fun i => Tree.lt_of_le_of_ne (hfb i) (fun h => hfmax ⟨i, h⟩)
      have hlt : ∀ n : ℤ, Tree.lt (d.treeH (d.coeffToP ((f * g).1 n))) (T₁ * T₂) := by
        intro n
        rw [SkewLaurentSeries.mul_apply_eq_single_right f g j₀ n hgmono]
        have hbase := treeH_coeffToP_mul_ofAdd_le d f g n (n - j₀)
        rw [show n - (n - j₀) = j₀ by omega] at hbase
        refine Tree.lt_of_le_of_lt' hbase ?_
        rw [hj₀]
        exact Tree.lt_mul_right (hf_lt (n - j₀)) hT₂
      refine ⟨f * g, hFG, fun n => Tree.le_of_lt (hlt n), fun n hn j hj => ?_⟩
      exact absurd (hn ▸ hlt n) Tree.lt_irrefl
    · -- no coefficient of either factor attains its bound: the `dlog` of *every* summand of the
      -- `n`-th coefficient is strictly below `some (A + B)`, whence the `dlog` of the coefficient
      -- is too and the coefficient is strictly below `T₁ * T₂ = exp (A + B)`
      have hf_lt : ∀ i : ℤ, Tree.lt (d.treeH (d.coeffToP (f.1 i))) T₁ :=
        fun i => Tree.lt_of_le_of_ne (hfb i) (fun h => hfmax ⟨i, h⟩)
      have hg_lt : ∀ j : ℤ, Tree.lt (d.treeH (d.coeffToP (g.1 j))) T₂ :=
        fun j => Tree.lt_of_le_of_ne (hgb j) (fun h => hgmax ⟨j, h⟩)
      have hfO : ∀ i : ℤ, Tree.Olt (Tree.dlog (d.treeH (d.coeffToP (f.1 i)))) (some A) := by
        intro i
        exact Tree.olt_dlog_of_lt_exp (by rw [← hT₁e]; exact hf_lt i)
      have hgO : ∀ j : ℤ, Tree.Olt (Tree.dlog (d.treeH (d.coeffToP (g.1 j)))) (some B) := by
        intro j
        exact Tree.olt_dlog_of_lt_exp (by rw [← hT₂e]; exact hg_lt j)
      have hlt : ∀ n : ℤ, Tree.lt (d.treeH (d.coeffToP ((f * g).1 n))) (T₁ * T₂) := by
        intro n
        have hterm : ∀ k ∈ Finset.Icc (SkewLaurentSeries.lo f) (n - SkewLaurentSeries.lo g),
            Tree.Olt (Tree.dlog (d.treeH (d.coeffToP
              (f.1 k * ((Multiplicative.ofAdd k) • g.1 (n - k)))))) (some (A + B)) :=
          fun k _ => olt_dlog_coeffToP_mul_ofAdd d f g n k (hfO k) (hgO (n - k))
        have hsum := Tree.olt_dlog_sum
          (Finset.Icc (SkewLaurentSeries.lo f) (n - SkewLaurentSeries.lo g))
          (fun k => d.treeH (d.coeffToP (f.1 k * ((Multiplicative.ofAdd k) • g.1 (n - k)))))
          (A + B) hterm
        have hle := treeH_le_sum
          (Finset.Icc (SkewLaurentSeries.lo f) (n - SkewLaurentSeries.lo g))
          (fun k => d.coeffToP (f.1 k * ((Multiplicative.ofAdd k) • g.1 (n - k))))
          (fun k _ => d.coeffToP_mem _)
        have hcoeff : d.coeffToP ((f * g).1 n) =
            ∑ k ∈ Finset.Icc (SkewLaurentSeries.lo f) (n - SkewLaurentSeries.lo g),
              d.coeffToP (f.1 k * ((Multiplicative.ofAdd k) • g.1 (n - k))) := by
          rw [SkewLaurentSeries.mul_apply]
          exact map_sum (Subring.subtype DN) _ _
        have h1 : Tree.Ole (Tree.dlog (d.treeH (d.coeffToP ((f * g).1 n))))
            (Tree.dlog (∑ k ∈ Finset.Icc (SkewLaurentSeries.lo f) (n - SkewLaurentSeries.lo g),
              d.treeH (d.coeffToP (f.1 k * ((Multiplicative.ofAdd k) • g.1 (n - k)))))) := by
          rw [hcoeff]
          exact Tree.ole_dlog_of_le hle
        have h2 : Tree.Olt (Tree.dlog (d.treeH (d.coeffToP ((f * g).1 n)))) (some (A + B)) :=
          Tree.ole_olt_trans h1 hsum
        exact Tree.lt_of_olt_dlog (by rw [hAB]; exact h2)
      refine ⟨f * g, hFG, fun n => Tree.le_of_lt (hlt n), fun n hn j hj => ?_⟩
      exact absurd (hn ▸ hlt n) Tree.lt_irrefl

end Work.ORHughesFree.Prop51
