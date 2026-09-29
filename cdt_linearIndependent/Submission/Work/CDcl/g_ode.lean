import Mathlib
import Submission.Work.CDcl.setup
import Submission.Work.CDcl.invsum
import Submission.Work.CDcl.g_rel
import Submission.Work.CDcl.order_raise
import Submission.Work.CDcl.sympoly_map_eq_zero

/-! Guidance from the requester (Area CDCl of `cdt_linearIndependent`):

# The order-4 ODE for `G = Sym⁺P` (the hard half of `CDClosed`)

`Submission/Work/CDcl/setup.lean` defines `G0 a b ra rb rab r0 = Submission.CDT.sympSym
(Submission.CDT.logP a b ra rb rab r0)` and `T a b ra rb rab r0 k = ((PowerSeries.derivative (R := ℚ))^[k] G0).subst
sympY`.  Available (already proved in this workspace, import them):
* `Work.CDcl.inv_sum` (`Submission.Work.CDcl.invsum`): for a polynomial `P ∈ ℚ[x]` there are
  `p q ∈ ℚ[y]`, `q ≠ 0`, with `q(y)·(P(x) + P(x/(x-1))) = p(y)` as power series in `x`.
* `Work.CDcl.x_relation` (`Submission.Work.CDcl.x_relation`): for all `a b : ℚ`, `ra rb rab r0 : ℤ`
  there are `P : Fin 5 → ℚ[x]`, `r : ℚ[x]`, `P ≠ 0`, with `Σ_{k<5} (P k)·T k = r` as power series.

What is asked: the order-4 inhomogeneous relation for `G`: there are `q ∈ ℚ[y]`, `q ≠ 0`,
`A : Fin 4 → ℚ[y]` and `c ∈ ℚ[y]` with
  `q · G'''' = Σ_{k<4} A k · G^{(k)} + c`  (as power series in `y`).

Suggested route (this is exactly the argument that makes the paper's `LL(G) ∈ ℚ[y]` unnecessary).
Write `σ` for the substitution `x ↦ x/(x-1)` on power series (`PowerSeries.subst sympPhi`), so
`(T k).subst sympPhi = T k` (because `T k = F.subst sympY` and `sympY.subst sympPhi = sympY`, via
`PowerSeries.subst_comp_subst_apply` + `Submission.CDT.symp_y_invariant`).

1. From `Σ_k (P k)·T k = r` and its σ-conjugate `Σ_k (σ(P k))·T k = σ r` (apply `subst sympPhi`
   to both sides, using `PowerSeries.subst_add/mul` and `T k`-invariance), add to get
   `Σ_k ((P k) + σ(P k))·T k = r + σ r`, an identity of power series in `x`.
2. Apply `inv_sum` to each `P k` and to `r`: get `p k, q k` and `p0, q0`.  Multiply the relation by
   `(∏_k q k(y)) · q0(y)` and use `q k(y)·((P k) + σ(P k)) = p k(y)` to obtain, with
   `D k := q0 · (∏_{j ≠ k} q j) · p k ∈ ℚ[y]` and `c := (∏_k q k) · p0 ∈ ℚ[y]`:
   `Σ_k D k(y)·T k = c(y)` (an identity of power series in `x`).
   If this relation is trivial (`D = 0` and `c = 0`; this happens only when every
   `P k + σ(P k) = 0` and `r + σr = 0`), use instead the *difference*
   `Σ_k ((P k) − σ(P k))·T k = r − σ r` and a descent for the σ-anti-invariant series
   `(P k) − σ(P k) = (x − x/(x-1))·g k` with `g k` σ-invariant (`symp_descent`,
   `Submission.CDT.symp_subst_y_injective`; or apply `inv_sum` to `both` `P k` and its conjugate
   and subtract the two cleared relations).
3. Since `T k = ((PowerSeries.derivative (R := ℚ))^[k] G0).subst sympY`, the identity of step 2 is the pullback along
   `y` of `Σ_k D k · G^{(k)} = c`; conclude with `Submission.CDT.symp_subst_y_injective`.
4. Finish: if `D 4 ≠ 0`, read the relation as `D 4·G'''' = c − Σ_{k<4} D k·G^{(k)}` (take
   `q := D 4`, `A k := −D k`, `c' := c`).  If `D 4 = 0` (the relation has order `d ≤ 3` with
   `D d ≠ 0`), differentiate the relation `4 − d` times: `(d/dy)` of `Σ_k D k·G^{(k)} = c` is
   `Σ_k (D k' + D (k−1))·G^{(k)} = c'` (Leibniz; coefficients stay in `ℚ[y]`), and this operation
   preserves the leading coefficient `D d` while raising the order by one; after `4 − d` steps the
   relation has order 4 with leading coefficient `D d ≠ 0`, giving the required `q ≠ 0`.

You may add helper lemmas above the statement; do not change the statement. -/

/-!
# `Work.CDcl.g_ode`: the order-4 inhomogeneous ODE for `G = Sym⁺P`

Proof outline (following the requester's route, with `inv_sum_aux` doing the clearing in one step
so that no denominator has to be carried around):

* `Work.CDcl.g_relation` (`Submission.Work.CDcl.g_rel`, this workspace's independent route: it
  reproves the pulled-back order-two ODE `g_ode_Pw` for `Pw = P∘φ` in `ℚ((x))`) gives
  `P : Fin 5 → ℚ[x]`, `r ∈ ℚ[x]`, `P ≠ 0`, `Σ_k (P k)·T k = r`.
* Applying the involution `σ = subst sympPhi` to this identity (each `T k` is `σ`-invariant,
  `gode_T_invariant`) and adding gives `Σ_k ((P k) + σ(P k))·T k = r + σ r`.
* `inv_sum_aux` identifies `(P k) + σ(P k)` with `(D k)(y)` where
  `D k = Σ_j (coeff j (P k))·symPoly j ∈ ℚ[y]` (and `r + σ r = c(y)` likewise).  `D ≠ 0` because
  `D k = 0` forces `P k = 0` (`sympoly_map_eq_zero`); so the triviality case of the requester's
  step 2 never occurs and no descent for anti-invariant series is needed.
* Unfolding `T k = (G^{(k)})∘y` and using injectivity of `subst sympY`
  (`symp_subst_y_injective`) yields the identity `Σ_k (D k)·G^{(k)} = c` in `ℚ[[y]]`.
* `order_raise` raises the (possibly lower order) relation to a genuine order-4 relation. -/


noncomputable section

namespace Work.CDcl

open Polynomial PowerSeries

open scoped BigOperators

/-- `T k` is fixed by `x ↦ x/(x-1)` -/
theorem gode_T_invariant (a b : ℚ) (ra rb rab r0 : ℤ) (k : ℕ) :
    (T a b ra rb rab r0 k).subst Submission.CDT.sympPhi = T a b ra rb rab r0 k := by
  unfold T
  rw [PowerSeries.subst_comp_subst_apply (R := ℚ) Submission.CDT.sympY_hasSubst
    Submission.CDT.sympPhi_hasSubst]
  rw [Submission.CDT.symp_y_invariant]

theorem gode_subst_sum_phi {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℚ) :
    (∑ i ∈ s, f i).subst Submission.CDT.sympPhi
      = ∑ i ∈ s, (f i).subst Submission.CDT.sympPhi := by
  rw [← PowerSeries.coe_substAlgHom Submission.CDT.sympPhi_hasSubst]
  exact map_sum (PowerSeries.substAlgHom Submission.CDT.sympPhi_hasSubst) f s

theorem gode_subst_sum_y {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℚ) :
    (∑ i ∈ s, f i).subst Submission.CDT.sympY
      = ∑ i ∈ s, (f i).subst Submission.CDT.sympY := by
  rw [← PowerSeries.coe_substAlgHom Submission.CDT.sympY_hasSubst]
  exact map_sum (PowerSeries.substAlgHom Submission.CDT.sympY_hasSubst) f s

theorem g_ode (a b : ℚ) (ra rb rab r0 : ℤ) :
    ∃ (q : Polynomial ℚ) (A : Fin 4 → Polynomial ℚ) (c : Polynomial ℚ), q ≠ 0 ∧
      (q : PowerSeries ℚ) * (PowerSeries.derivative (R := ℚ))^[4] (Work.CDcl.G0 a b ra rb rab r0)
        = (∑ k : Fin 4, (A k : PowerSeries ℚ)
            * (PowerSeries.derivative (R := ℚ))^[k] (Work.CDcl.G0 a b ra rb rab r0))
          + (c : PowerSeries ℚ) := by
    obtain ⟨P, r, hP, hrel⟩ := g_relation a b ra rb rab r0
    set D : Fin 5 → Polynomial ℚ :=
      fun k => (P k).sum (fun j x => Polynomial.C x * symPoly j) with hDdef
    set c : Polynomial ℚ := r.sum (fun j x => Polynomial.C x * symPoly j) with hcdef
    have hDne : D ≠ 0 := by
      intro h0
      apply hP
      funext k
      have hk : (P k).sum (fun j x => Polynomial.C x * symPoly j) = 0 := by
        have h1 : D k = 0 := by simp [h0]
        simpa [hDdef] using h1
      exact sympoly_map_eq_zero.mp hk
    have key : (∑ k : Fin 5, (D k : PowerSeries ℚ)
          * (PowerSeries.derivative (R := ℚ))^[k] (G0 a b ra rb rab r0)) = (c : PowerSeries ℚ) := by
      have hconj : (∑ k : Fin 5, (P k : PowerSeries ℚ).subst Submission.CDT.sympPhi
            * T a b ra rb rab r0 k) = (r : PowerSeries ℚ).subst Submission.CDT.sympPhi := by
        have h1 := congrArg (fun z : PowerSeries ℚ => z.subst Submission.CDT.sympPhi) hrel
        rw [gode_subst_sum_phi] at h1
        have hterm : ∀ k : Fin 5,
            PowerSeries.subst Submission.CDT.sympPhi ((P k : PowerSeries ℚ) * T a b ra rb rab r0 k)
              = (P k : PowerSeries ℚ).subst Submission.CDT.sympPhi * T a b ra rb rab r0 k := by
          intro k
          rw [PowerSeries.subst_mul Submission.CDT.sympPhi_hasSubst, gode_T_invariant]
        simpa only [hterm] using h1
      have hPk : ∀ k : Fin 5, ((P k : PowerSeries ℚ)
            + (P k : PowerSeries ℚ).subst Submission.CDT.sympPhi)
          = (D k : PowerSeries ℚ).subst Submission.CDT.sympY := by
        intro k
        simpa [hDdef] using inv_sum_aux (P k)
      have hr : ((r : PowerSeries ℚ) + (r : PowerSeries ℚ).subst Submission.CDT.sympPhi)
          = (c : PowerSeries ℚ).subst Submission.CDT.sympY := by
        simpa [hcdef] using inv_sum_aux r
      have hsum : (∑ k : Fin 5, ((P k : PowerSeries ℚ)
              + (P k : PowerSeries ℚ).subst Submission.CDT.sympPhi) * T a b ra rb rab r0 k)
          = (r : PowerSeries ℚ) + (r : PowerSeries ℚ).subst Submission.CDT.sympPhi := by
        have h : (∑ k : Fin 5, (P k : PowerSeries ℚ) * T a b ra rb rab r0 k)
              + (∑ k : Fin 5, (P k : PowerSeries ℚ).subst Submission.CDT.sympPhi
                  * T a b ra rb rab r0 k)
            = (r : PowerSeries ℚ) + (r : PowerSeries ℚ).subst Submission.CDT.sympPhi := by
          rw [hrel, hconj]
        rw [← Finset.sum_add_distrib] at h
        have h2 : ∀ k : Fin 5, (P k : PowerSeries ℚ) * T a b ra rb rab r0 k
                + (P k : PowerSeries ℚ).subst Submission.CDT.sympPhi * T a b ra rb rab r0 k
              = ((P k : PowerSeries ℚ) + (P k : PowerSeries ℚ).subst Submission.CDT.sympPhi)
                * T a b ra rb rab r0 k := fun k => by ring
        simpa only [h2] using h
      have h4 : (∑ k : Fin 5, ((D k : PowerSeries ℚ).subst Submission.CDT.sympY)
            * T a b ra rb rab r0 k) = (c : PowerSeries ℚ).subst Submission.CDT.sympY := by
        simpa only [hPk, hr] using hsum
      have hT : ∀ k : ℕ, T a b ra rb rab r0 k
          = ((PowerSeries.derivative (R := ℚ))^[k] (G0 a b ra rb rab r0)).subst Submission.CDT.sympY :=
        fun k => rfl
      have h5 : (∑ k : Fin 5, (((D k : Polynomial ℚ) : PowerSeries ℚ)
              * (PowerSeries.derivative (R := ℚ))^[k] (G0 a b ra rb rab r0)).subst Submission.CDT.sympY)
          = (c : PowerSeries ℚ).subst Submission.CDT.sympY := by
        have hterm : ∀ k : Fin 5, ((D k : PowerSeries ℚ).subst Submission.CDT.sympY)
              * T a b ra rb rab r0 k
            = (((D k : Polynomial ℚ) : PowerSeries ℚ)
                * (PowerSeries.derivative (R := ℚ))^[k] (G0 a b ra rb rab r0)).subst Submission.CDT.sympY := by
          intro k
          rw [hT, ← PowerSeries.subst_mul Submission.CDT.sympY_hasSubst]
        simpa only [hterm] using h4
      have h6 : ((∑ k : Fin 5, (D k : PowerSeries ℚ)
              * (PowerSeries.derivative (R := ℚ))^[k] (G0 a b ra rb rab r0))).subst Submission.CDT.sympY
          = (c : PowerSeries ℚ).subst Submission.CDT.sympY := by
        rw [← gode_subst_sum_y] at h5
        exact h5
      have h7 : (∑ k : Fin 5, (D k : PowerSeries ℚ)
              * (PowerSeries.derivative (R := ℚ))^[k] (G0 a b ra rb rab r0)) - (c : PowerSeries ℚ) = 0 := by
        apply Submission.CDT.symp_subst_y_injective
        rw [PowerSeries.subst_sub Submission.CDT.sympY_hasSubst, h6]
        ring
      exact sub_eq_zero.mp h7
    obtain ⟨q, A, c', hq, hfin⟩ := order_raise (G0 a b ra rb rab r0) D c hDne key
    exact ⟨q, A, c', hq, hfin⟩

end Work.CDcl
