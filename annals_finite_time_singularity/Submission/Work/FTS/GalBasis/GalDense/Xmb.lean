/-
# `GalDense.Xmb` — a clash-free copy of `Work.FTS.GalBasis.exists_mixed_bound`

The file `Submission/Work/FTS/GalBasis/exists_mixed_bound.lean` declares
`Work.FTS.GalBasis.contDiffOn_uncurry_{pz,pth,pzIter,pthIter}_le`, the very names that
`Submission/Work/FTS/GalBasis/FamEAux/Basic.lean` also declares; the two modules therefore
cannot be imported into one environment, which blocks `ApproxCC/FamEApprox.lean` (a file that
needs both) and with it the density chain of `dense_famGood.lean`.

This module is a byte-for-byte copy of that file with every declaration placed in the
*sub*nemsapce `Work.FTS.GalBasis.Xmb`, so that it imports together with `FamEAux.Basic`
without a clash.  Nothing here is new mathematics.
-/
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.scoef
import Submission.Work.Spaces.scoef_sum_shift
import Submission.Work.Spaces.pz_aux
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.FTS.EllipticEst.remov.high_chain_sum_self

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalBasis.Xmb

open scoped Real Topology ContDiff
open Set Filter

open Work.FTS.EllipticEst.remov.selfdth (dthCoef DthIter_expansion_of_contDiffOn
  DthCoef_sin_pow_bound)

noncomputable section

set_option autoImplicit false

/-! ## Smoothness of the curried partial derivatives, at a finite order

The `ℋ^k`-machinery of the project uses `ContDiffOn ℝ ⊤` on the fixed sets of
`Work.Spaces`; here the data is only `C⁶` on an arbitrary rectangle, so the
partial-derivative calculus is re-stated at a finite order on an arbitrary open set.
-/

/-- The `z`-partial derivative lowers the order of differentiability by one. -/
theorem contDiffOn_uncurry_pz_le {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) {n : ℕ}
    (h : ContDiffOn ℝ (((n + 1 : ℕ)) : WithTop ℕ∞) (Function.uncurry G) V) :
    ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (Function.uncurry (Work.Spaces.pz G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pz G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (1, 0) := fun p hp =>
    Work.Spaces.pz_eq_fderiv ((h.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V :=
    h.fderiv_of_isOpen hV (by simp)
  have hcomp : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (1, 0)) V := by
    simpa using hfd.clm_apply
      (contDiffOn_const : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (fun _ : ℝ × ℝ => ((1, 0) : ℝ × ℝ)) V)
  exact hcomp.congr hchain

/-- The `θ`-partial derivative lowers the order of differentiability by one. -/
theorem contDiffOn_uncurry_pth_le {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) {n : ℕ}
    (h : ContDiffOn ℝ (((n + 1 : ℕ)) : WithTop ℕ∞) (Function.uncurry G) V) :
    ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (Function.uncurry (Work.Spaces.pth G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pth G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (0, 1) := fun p hp =>
    Work.Spaces.pth_eq_fderiv ((h.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V :=
    h.fderiv_of_isOpen hV (by simp)
  have hcomp : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (0, 1)) V := by
    simpa using hfd.clm_apply
      (contDiffOn_const : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (fun _ : ℝ × ℝ => ((0, 1) : ℝ × ℝ)) V)
  exact hcomp.congr hchain

/-- The iterated `z`-partial `∂_z^i` costs `i` orders of differentiability. -/
theorem contDiffOn_uncurry_pzIter_le {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) {N : ℕ}
    (h : ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) (Function.uncurry G) V) :
    ∀ i k : ℕ, i + k ≤ N →
      ContDiffOn ℝ ((k : ℕ) : WithTop ℕ∞) (Function.uncurry (Work.Spaces.pzIter i G)) V := by
  intro i
  induction i with
  | zero => intro k hk; simpa using h.of_le (Nat.cast_le.mpr (show k ≤ N by omega))
  | succ i ih =>
      intro k hik
      have h2 : ContDiffOn ℝ (((k + 1 : ℕ)) : WithTop ℕ∞)
          (Function.uncurry (Work.Spaces.pzIter i G)) V := ih (k + 1) (by omega)
      simpa [Work.Spaces.pzIter_succ] using contDiffOn_uncurry_pz_le hV h2

/-- The iterated `θ`-partial `∂_θ^i` costs `i` orders of differentiability. -/
theorem contDiffOn_uncurry_pthIter_le {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) {N : ℕ}
    (h : ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) (Function.uncurry G) V) :
    ∀ i k : ℕ, i + k ≤ N →
      ContDiffOn ℝ ((k : ℕ) : WithTop ℕ∞) (Function.uncurry (Work.Spaces.pthIter i G)) V := by
  intro i
  induction i with
  | zero => intro k hk; simpa using h.of_le (Nat.cast_le.mpr (show k ≤ N by omega))
  | succ i ih =>
      intro k hik
      have h2 : ContDiffOn ℝ (((k + 1 : ℕ)) : WithTop ℕ∞)
          (Function.uncurry (Work.Spaces.pthIter i G)) V := ih (k + 1) (by omega)
      simpa [Work.Spaces.pthIter_succ] using contDiffOn_uncurry_pth_le hV h2

/-- The `z`-slice of a function that is `C^N` on an open set is `C^N` at the point. -/
theorem contDiffAt_slice_fst_of_uncurry {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    {N : ℕ} (h : ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) (Function.uncurry G) V)
    {z θ : ℝ} (hz : (z, θ) ∈ V) :
    ContDiffAt ℝ ((N : ℕ) : WithTop ℕ∞) (fun z' => G z' θ) z := by
  have hc : ContDiffAt ℝ ((N : ℕ) : WithTop ℕ∞) (Function.uncurry G) (z, θ) :=
    h.contDiffAt (hV.mem_nhds hz)
  have hlin : ContDiffAt ℝ ((N : ℕ) : WithTop ℕ∞) (fun z' : ℝ => (z', θ)) z := by fun_prop
  simpa [Function.comp_def, Function.uncurry] using hc.comp z hlin

/-- Differentiability of the `z`-slice of an iterated `z`-partial, at a point of an open
set where the function is smooth enough. -/
theorem differentiableAt_slice_pzIter {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    {N : ℕ} (h : ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) (Function.uncurry G) V)
    {i : ℕ} (hi : i + 1 ≤ N) {z θ : ℝ} (hz : (z, θ) ∈ V) :
    DifferentiableAt ℝ (fun z' => Work.Spaces.pzIter i G z' θ) z := by
  have h1 : ContDiffOn ℝ ((1 : ℕ) : WithTop ℕ∞)
      (Function.uncurry (Work.Spaces.pzIter i G)) V :=
    contDiffOn_uncurry_pzIter_le hV h i 1 (by omega)
  have h2 : ContDiffAt ℝ ((1 : ℕ) : WithTop ℕ∞)
      (fun z' => Work.Spaces.pzIter i G z' θ) z :=
    contDiffAt_slice_fst_of_uncurry hV h1 hz
  exact h2.differentiableAt (by simp)

/-- Smoothness of the `z`-slice of an iterated `θ`-partial. -/
theorem contDiffAt_slice_pthIter {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) {N : ℕ}
    (h : ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) (Function.uncurry G) V)
    {i k : ℕ} (hi : i + k ≤ N) {z θ : ℝ} (hz : (z, θ) ∈ V) :
    ContDiffAt ℝ ((k : ℕ) : WithTop ℕ∞) (fun z' => Work.Spaces.pthIter i G z' θ) z :=
  contDiffAt_slice_fst_of_uncurry hV (contDiffOn_uncurry_pthIter_le hV h i k hi) hz

/-! ## The expansion of `D_z^n = (z∂_z)^n` in Stirling numbers -/

/-- The derivative of `z ↦ z^k`. -/
private theorem deriv_zpow (k : ℕ) (z : ℝ) :
    deriv (fun z' : ℝ => z' ^ k) z = (k : ℝ) * z ^ (k - 1) := by
  have h := deriv_pow (f := fun z' : ℝ => z') (x := z) differentiableAt_id k
  rw [show (fun z' : ℝ => z') ^ k = (fun z' : ℝ => z' ^ k) from rfl] at h
  have h1 : deriv (fun z' : ℝ => z') z = 1 := deriv_id z
  rw [h, h1]
  ring

/-- The elementary algebra of one term of the induction step. -/
private theorem z_mul_term (k : ℕ) (z A B : ℝ) :
    z * ((k : ℝ) * z ^ (k - 1) * A + z ^ k * B) = (k : ℝ) * z ^ k * A + z ^ (k + 1) * B := by
  rcases k with _ | m
  · ring
  · rw [pow_succ]; push_cast; ring

/-- **The Stirling expansion of `D_z^n`**, at a point where the `z`-slice of `h` is
`C^{n+1}` on an open set contained in the domain:
`D_z^n h = ∑_{k ≤ n} S(n,k) z^k ∂_z^k h`. -/
theorem DzIter_eq_sum_scoef_of_contDiffOn (h : ℝ → ℝ → ℝ) (U : Set (ℝ × ℝ)) (hU : IsOpen U) :
    ∀ n : ℕ, ContDiffOn ℝ (((n + 1 : ℕ)) : WithTop ℕ∞) (Function.uncurry h) U →
      ∀ z θ, (z, θ) ∈ U →
        Work.Spaces.DzIter n h z θ =
          ∑ k ∈ Finset.range (n + 1), (Work.Spaces.scoef n k : ℝ) * (z ^ k * Work.Spaces.pzIter k h z θ) := by
  intro n
  induction n with
  | zero =>
      intro hsm z θ hzθ
      rw [Finset.sum_range_one, show Work.Spaces.scoef 0 0 = 1 from rfl]
      norm_num
  | succ n ih =>
      intro hsm z θ hzθ
      have hsm' : ContDiffOn ℝ (((n + 1 : ℕ)) : WithTop ℕ∞) (Function.uncurry h) U :=
        hsm.of_le (Nat.cast_le.mpr (show n + 1 ≤ n + 2 by omega))
      have hdiff : ∀ k : ℕ, k ≤ n →
          DifferentiableAt ℝ (fun z' => Work.Spaces.pzIter k h z' θ) z := fun k hk =>
        differentiableAt_slice_pzIter hU hsm (i := k) (by omega) hzθ
      have hd1 : ∀ k : ℕ, DifferentiableAt ℝ (fun z' : ℝ => z' ^ k) z := fun k =>
        differentiableAt_pow k
      have hd3 : ∀ k ∈ Finset.range (n + 1),
          DifferentiableAt ℝ (fun z' : ℝ => z' ^ k * Work.Spaces.pzIter k h z' θ) z :=
        fun k hk => (hd1 k).mul (hdiff k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)))
      have hsl : {z' : ℝ | (z', θ) ∈ U} ∈ 𝓝 z := by
        have hopen : IsOpen {z' : ℝ | (z', θ) ∈ U} :=
          hU.preimage (by fun_prop : Continuous fun z' : ℝ => (z', θ))
        exact hopen.mem_nhds hzθ
      have hev : (fun z' => Work.Spaces.DzIter n h z' θ)
          =ᶠ[𝓝 z] (fun z' => ∑ k ∈ Finset.range (n + 1),
              (Work.Spaces.scoef n k : ℝ) * (z' ^ k * Work.Spaces.pzIter k h z' θ)) := by
        filter_upwards [hsl] with z' hz'
        exact ih hsm' z' θ hz'
      have hterm : ∀ k : ℕ, k ≤ n →
          deriv (fun z' : ℝ => (Work.Spaces.scoef n k : ℝ) * (z' ^ k * Work.Spaces.pzIter k h z' θ)) z
            = (Work.Spaces.scoef n k : ℝ)
                * ((k : ℝ) * z ^ (k - 1) * Work.Spaces.pzIter k h z θ
                    + z ^ k * Work.Spaces.pzIter (k + 1) h z θ) := by
        intro k hk
        rw [deriv_const_mul (d := fun z' : ℝ => z' ^ k * Work.Spaces.pzIter k h z' θ)
          (Work.Spaces.scoef n k : ℝ) ((hd1 k).mul (hdiff k hk))]
        congr 1
        rw [show (fun z' : ℝ => z' ^ k * Work.Spaces.pzIter k h z' θ)
              = (fun z' : ℝ => z' ^ k) * (fun z' : ℝ => Work.Spaces.pzIter k h z' θ) from rfl,
          deriv_mul (hd1 k) (hdiff k hk), deriv_zpow]
        rfl
      have hderiv : deriv (fun z' => Work.Spaces.DzIter n h z' θ) z
          = ∑ k ∈ Finset.range (n + 1), (Work.Spaces.scoef n k : ℝ)
              * ((k : ℝ) * z ^ (k - 1) * Work.Spaces.pzIter k h z θ
                  + z ^ k * Work.Spaces.pzIter (k + 1) h z θ) := by
        rw [hev.deriv_eq]
        have hsumfun : (fun z' => ∑ k ∈ Finset.range (n + 1),
              (Work.Spaces.scoef n k : ℝ) * (z' ^ k * Work.Spaces.pzIter k h z' θ))
            = (∑ k ∈ Finset.range (n + 1),
                fun z' => (Work.Spaces.scoef n k : ℝ) * (z' ^ k * Work.Spaces.pzIter k h z' θ)) := by
          funext z'
          simp [Finset.sum_apply]
        rw [hsumfun, deriv_sum (fun k hk => (hd3 k hk).const_mul (Work.Spaces.scoef n k : ℝ))]
        exact Finset.sum_congr rfl fun k hk =>
          hterm k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
      calc Work.Spaces.DzIter (n + 1) h z θ
          = z * deriv (fun z' => Work.Spaces.DzIter n h z' θ) z := by
            simp [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
        _ = z * (∑ k ∈ Finset.range (n + 1), (Work.Spaces.scoef n k : ℝ)
              * ((k : ℝ) * z ^ (k - 1) * Work.Spaces.pzIter k h z θ
                  + z ^ k * Work.Spaces.pzIter (k + 1) h z θ)) := by rw [hderiv]
        _ = ∑ k ∈ Finset.range (n + 1), (Work.Spaces.scoef n k : ℝ)
              * ((k : ℝ) * z ^ k * Work.Spaces.pzIter k h z θ
                  + z ^ (k + 1) * Work.Spaces.pzIter (k + 1) h z θ) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [show z * ((Work.Spaces.scoef n k : ℝ)
                  * ((k : ℝ) * z ^ (k - 1) * Work.Spaces.pzIter k h z θ
                      + z ^ k * Work.Spaces.pzIter (k + 1) h z θ))
                = (Work.Spaces.scoef n k : ℝ)
                  * (z * ((k : ℝ) * z ^ (k - 1) * Work.Spaces.pzIter k h z θ
                      + z ^ k * Work.Spaces.pzIter (k + 1) h z θ)) from by ring,
              z_mul_term]
        _ = ∑ j ∈ Finset.range (n + 2),
              (Work.Spaces.scoef (n + 1) j : ℝ) * (z ^ j * Work.Spaces.pzIter j h z θ) :=
            Work.Spaces.scoef_sum_shift n (fun k => Work.Spaces.pzIter k h z θ) z

/-- **The angular expansion commutes with `∂_z^k`**: on an open set where `F` is smooth
enough, the `k`-th `z`-derivative of the exact expansion of `D_θ^b` is the expansion of the
`k`-th `z`-derivative. -/
theorem pzIter_DthIter_expansion {F : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U) {N : ℕ}
    (hF : ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) (Function.uncurry F) U)
    {b k : ℕ} (hb1 : b + 1 ≤ N) (hbk : b + k ≤ N) {z θ : ℝ} (hzθ : (z, θ) ∈ U) :
    Work.Spaces.pzIter k (Work.Spaces.DthIter b F) z θ
      = ∑ r ∈ Finset.range (b + 1), dthCoef b r θ * Work.Spaces.pzIter k (Work.Spaces.pthIter r F) z θ := by
  have hexp : ∀ z' θ' : ℝ, (z', θ') ∈ U →
      Work.Spaces.DthIter b F z' θ'
        = ∑ r ∈ Finset.range (b + 1), dthCoef b r θ' * Work.Spaces.pthIter r F z' θ' :=
    fun z' θ' h => DthIter_expansion_of_contDiffOn b F U hU
      (hF.of_le (Nat.cast_le.mpr hb1)) z' θ' h
  have hsl : {z' : ℝ | (z', θ) ∈ U} ∈ 𝓝 z := by
    have hopen : IsOpen {z' : ℝ | (z', θ) ∈ U} :=
      hU.preimage (by fun_prop : Continuous fun z' : ℝ => (z', θ))
    exact hopen.mem_nhds hzθ
  have hev : (fun z' => Work.Spaces.DthIter b F z' θ)
      =ᶠ[𝓝 z] (fun z' => ∑ r ∈ Finset.range (b + 1),
          dthCoef b r θ * Work.Spaces.pthIter r F z' θ) := by
    filter_upwards [hsl] with z' hz'
    exact hexp z' θ hz'
  calc Work.Spaces.pzIter k (Work.Spaces.DthIter b F) z θ
      = iteratedDeriv k (fun z' => Work.Spaces.DthIter b F z' θ) z :=
        Work.Spaces.pzIter_eq_iteratedDeriv k _ z θ
    _ = iteratedDeriv k (fun z' => ∑ r ∈ Finset.range (b + 1),
          dthCoef b r θ * Work.Spaces.pthIter r F z' θ) z := hev.iteratedDeriv_eq k
    _ = ∑ r ∈ Finset.range (b + 1),
          dthCoef b r θ * iteratedDeriv k (fun z' => Work.Spaces.pthIter r F z' θ) z :=
        Work.Spaces.iteratedDeriv_sum_const_mul _ (fun r => dthCoef b r θ)
          (fun r z' => Work.Spaces.pthIter r F z' θ) k z
          (fun r hr => contDiffAt_slice_pthIter hU hF
            (i := r) (k := k) (by
              have hr' : r ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
              omega) hzθ)
    _ = ∑ r ∈ Finset.range (b + 1),
          dthCoef b r θ * Work.Spaces.pzIter k (Work.Spaces.pthIter r F) z θ := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Work.Spaces.pzIter_eq_iteratedDeriv]

/-! ## The main bound

`D_z^a D_θ^b F` is a *finite linear combination*, with coefficients bounded on the box, of the
plain derivatives `∂_z^k ∂_θ^r F = pzIter k (pthIter r F)` with `k ≤ a`, `r ≤ b`:

* `D_z^a = ∑_{k≤a} S(a,k) z^k ∂_z^k` (Stirling numbers of the second kind,
  `DzIter_eq_sum_scoef_of_contDiffOn`);
* `∂_z^k (D_θ^b F) = ∑_{r≤b} a_{b,r}(θ) · ∂_z^k∂_θ^r F` (`pzIter_DthIter_expansion`, from the
  exact expansion `D_θ^b = ∑_r a_{b,r} ∂_θ^r` of `DthIter_expansion_of_contDiffOn` and the fact
  that the coefficients `a_{b,r}` do not depend on `z`),
* and `|a_{b,r}(θ)| ≤ K_{b,r} |sin 2θ|^r ≤ K_{b,r}` (`DthCoef_sin_pow_bound`), while
  `|z| ≤ max |A| |B|` on `[A,B]`.

Every `pzIter k (pthIter r F)` occurring has `k + r ≤ a + b ≤ 4`, so the hypothesis bounds it by
`M`, giving `|D_z^a D_θ^b F| ≤ K M` with
`K = (∑_{k≤a} S(a,k) (max |A| |B|)^k) · (∑_{r≤b} K_{b,r})`. -/

theorem exists_mixed_bound (a b : ℕ) (hab : a + b ≤ 4) (A B C D : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : ℝ → ℝ → ℝ) (M : ℝ), 0 ≤ M →
      ContDiffOn ℝ 6 (Function.uncurry F)
        (Set.Ioo (A - 1) (B + 1) ×ˢ Set.Ioo (C - 1) (D + 1)) →
      (∀ i j : ℕ, i + j ≤ 4 → ∀ z ∈ Set.Icc A B, ∀ θ ∈ Set.Icc C D,
          |Work.Spaces.pzIter i (Work.Spaces.pthIter j F) z θ| ≤ M) →
      ∀ z ∈ Set.Icc A B, ∀ θ ∈ Set.Icc C D,
        |Work.Spaces.mixed a b F z θ| ≤ K * M := by
  classical
  have hb4 : b ≤ 4 := by omega
  -- a uniform bound for the coefficients of `D_θ^b = ∑_{r ≤ b} a_{b,r} ∂_θ^r`
  choose Kc hKcpos hKcbd using fun r : ℕ => DthCoef_sin_pow_bound b r
  set Kcsum : ℝ := ∑ r ∈ Finset.range (b + 1), Kc r with hKcsum
  have hKcsum_nn : 0 ≤ Kcsum := by
    rw [hKcsum]; exact Finset.sum_nonneg fun r _ => (hKcpos r).le
  -- a bound for the powers of `z` on `[A,B]`
  set Z : ℝ := max |A| |B| with hZ
  have hZnn : 0 ≤ Z := by
    rw [hZ]; exact le_trans (abs_nonneg A) (le_max_left _ _)
  set Kz : ℝ := ∑ k ∈ Finset.range (a + 1), (Work.Spaces.scoef a k : ℝ) * Z ^ k with hKz
  have hKz_nn : 0 ≤ Kz := by
    rw [hKz]
    exact Finset.sum_nonneg fun k _ =>
      mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hZnn k)
  refine ⟨Kz * Kcsum, mul_nonneg hKz_nn hKcsum_nn, ?_⟩
  intro F M hM hsm hbd z hz θ hθ
  -- the open rectangle
  set U : Set (ℝ × ℝ) := Set.Ioo (A - 1) (B + 1) ×ˢ Set.Ioo (C - 1) (D + 1) with hUdef
  have hUopen : IsOpen U := by rw [hUdef]; exact isOpen_Ioo.prod isOpen_Ioo
  have hsmU : ContDiffOn ℝ 6 (Function.uncurry F) U := by rw [hUdef]; exact hsm
  have hzU : z ∈ Set.Ioo (A - 1) (B + 1) := ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have hθU : θ ∈ Set.Ioo (C - 1) (D + 1) := ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have hzθU : (z, θ) ∈ U := by rw [hUdef]; exact ⟨hzU, hθU⟩
  -- `|z| ≤ Z` on the box
  have hzZ : |z| ≤ Z := by
    rw [hZ]
    refine abs_le.mpr ⟨?_, ?_⟩
    · have h1 : |A| ≤ max |A| |B| := le_max_left _ _
      linarith [neg_abs_le A, hz.1, h1]
    · have h1 : |B| ≤ max |A| |B| := le_max_right _ _
      linarith [le_abs_self B, hz.2, h1]
  -- the joint smoothness of `D_θ^b F` on `U`, from its exact expansion
  have hsmDth : ContDiffOn ℝ (((a + 1 : ℕ)) : WithTop ℕ∞)
      (Function.uncurry (Work.Spaces.DthIter b F)) U := by
    have hcoef : ∀ r : ℕ, ContDiffOn ℝ (((a + 1 : ℕ)) : WithTop ℕ∞)
        (fun p : ℝ × ℝ => dthCoef b r p.2) U := by
      intro r
      have h1 : ContDiff ℝ (⊤ : ℕ∞) (dthCoef b r) :=
        Work.FTS.EllipticEst.remov.selfdth.contDiff_dthCoef b r
      exact ((h1.comp contDiff_snd).contDiffOn).of_le
        (by exact_mod_cast (le_top : (((a + 1 : ℕ)) : ℕ∞) ≤ ⊤))
    have hsum : ContDiffOn ℝ (((a + 1 : ℕ)) : WithTop ℕ∞)
        (fun p : ℝ × ℝ => ∑ r ∈ Finset.range (b + 1),
            dthCoef b r p.2 * Work.Spaces.pthIter r F p.1 p.2) U := by
      refine ContDiffOn.sum fun r hr => ?_
      have hr' : r ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
      have hra : r + (a + 1) ≤ 6 := by omega
      exact (hcoef r).mul (contDiffOn_uncurry_pthIter_le hUopen hsmU r (a + 1) hra)
    refine hsum.congr fun p hp => ?_
    show Work.Spaces.DthIter b F p.1 p.2 = ∑ r ∈ Finset.range (b + 1),
        dthCoef b r p.2 * Work.Spaces.pthIter r F p.1 p.2
    exact DthIter_expansion_of_contDiffOn b F U hUopen
      (hsmU.of_le (Nat.cast_le.mpr (show b + 1 ≤ 6 by omega))) p.1 p.2 hp
  -- the Stirling expansion of `D_z^a`
  have hStir : Work.Spaces.DzIter a (Work.Spaces.DthIter b F) z θ
      = ∑ k ∈ Finset.range (a + 1),
          (Work.Spaces.scoef a k : ℝ) * (z ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter b F) z θ) :=
    DzIter_eq_sum_scoef_of_contDiffOn (Work.Spaces.DthIter b F) U hUopen a hsmDth z θ hzθU
  -- the expansion of the `z`-derivatives of `D_θ^b F`
  have hL4 : ∀ k : ℕ, k ≤ a →
      Work.Spaces.pzIter k (Work.Spaces.DthIter b F) z θ
        = ∑ r ∈ Finset.range (b + 1),
            dthCoef b r θ * Work.Spaces.pzIter k (Work.Spaces.pthIter r F) z θ := by
    intro k hk
    have hbk : b + k ≤ 6 := by omega
    have hb1 : b + 1 ≤ 6 := by omega
    exact pzIter_DthIter_expansion (N := 6) hUopen hsmU hb1 hbk hzθU
  -- the bound on each `z`-derivative of `D_θ^b F`
  have hbound : ∀ k : ℕ, k ≤ a →
      |Work.Spaces.pzIter k (Work.Spaces.DthIter b F) z θ| ≤ Kcsum * M := by
    intro k hk
    rw [hL4 k hk]
    calc |∑ r ∈ Finset.range (b + 1),
            dthCoef b r θ * Work.Spaces.pzIter k (Work.Spaces.pthIter r F) z θ|
        ≤ ∑ r ∈ Finset.range (b + 1),
            |dthCoef b r θ * Work.Spaces.pzIter k (Work.Spaces.pthIter r F) z θ| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ r ∈ Finset.range (b + 1),
            |dthCoef b r θ| * |Work.Spaces.pzIter k (Work.Spaces.pthIter r F) z θ| := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [abs_mul]
      _ ≤ ∑ r ∈ Finset.range (b + 1), Kc r * M := by
          refine Finset.sum_le_sum fun r hr => ?_
          have hr' : r ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
          have h1 : |dthCoef b r θ| ≤ Kc r := by
            calc |dthCoef b r θ| ≤ Kc r * |Real.sin (2 * θ)| ^ r := hKcbd r θ
              _ ≤ Kc r * 1 := mul_le_mul_of_nonneg_left
                  (pow_le_one₀ (abs_nonneg _) (Real.abs_sin_le_one (2 * θ))) (hKcpos r).le
              _ = Kc r := mul_one _
          have h2 : |Work.Spaces.pzIter k (Work.Spaces.pthIter r F) z θ| ≤ M :=
            hbd k r (by omega) z hz θ hθ
          exact mul_le_mul h1 h2 (abs_nonneg _) (hKcpos r).le
      _ = Kcsum * M := by
          rw [hKcsum]
          exact (Finset.sum_mul (Finset.range (b + 1)) Kc M).symm
  -- assembly
  have hmain : |Work.Spaces.mixed a b F z θ| ≤ Kz * (Kcsum * M) := by
    show |Work.Spaces.DzIter a (Work.Spaces.DthIter b F) z θ| ≤ Kz * (Kcsum * M)
    rw [hStir]
    calc |∑ k ∈ Finset.range (a + 1),
            (Work.Spaces.scoef a k : ℝ) * (z ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter b F) z θ)|
        ≤ ∑ k ∈ Finset.range (a + 1), (Work.Spaces.scoef a k : ℝ)
            * (|z| ^ k * (Kcsum * M)) := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          refine Finset.sum_le_sum fun k hk => ?_
          have hk' : k ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
          rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (Work.Spaces.scoef a k)),
            abs_mul, abs_pow]
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          exact mul_le_mul_of_nonneg_left (hbound k hk') (pow_nonneg (abs_nonneg z) k)
      _ = (∑ k ∈ Finset.range (a + 1), (Work.Spaces.scoef a k : ℝ) * |z| ^ k)
            * (Kcsum * M) :=
          (Finset.sum_congr rfl fun k _ => by ring).trans
            (Finset.sum_mul (Finset.range (a + 1))
              (fun k => (Work.Spaces.scoef a k : ℝ) * |z| ^ k) (Kcsum * M)).symm
      _ ≤ (∑ k ∈ Finset.range (a + 1), (Work.Spaces.scoef a k : ℝ) * Z ^ k)
            * (Kcsum * M) := by
          refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hKcsum_nn hM)
          refine Finset.sum_le_sum fun k _ => ?_
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg z) hzZ k)
            (Nat.cast_nonneg _)
      _ = Kz * (Kcsum * M) := by rw [hKz]
  calc |Work.Spaces.mixed a b F z θ| ≤ Kz * (Kcsum * M) := hmain
    _ = (Kz * Kcsum) * M := by ring

end

end Work.FTS.GalBasis.Xmb
