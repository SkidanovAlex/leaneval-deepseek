import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Holder.holderNorm_mul_le
import Submission.Work.CR.Flat.Holder.holderNorm_add_le
import Submission.Work.CR.Flat.Holder.holderNorm_smul
import Submission.Work.CR.Flat.Holder.holderNorm_sum_le
import Submission.Work.CR.Flat.Holder.holderNorm_mono_alpha
import Submission.Work.NN.Final.Defs
import Submission.Work.NN.Final.holderNorm_one_comp_le
import Submission.Work.NN.Final.holderNorm_zero_mul_le
import Submission.Work.NN.Final.holderNorm_zero_clm_apply_le
import Submission.Work.CR.Flat.Holder.Bilinear
import Submission.Work.CR.Flat.Holder.holderNorm_neg
import Submission.Work.NN.Newton.pushforward_setup
import Submission.Work.NN.Newton.pushforward_norms
import Submission.Work.NN.Newton.nearInverseThin
import Submission.Work.NN.Newton.Minv_holderNorm_one_le
import Submission.Work.NN.Newton.holderNorm_one_fderiv_coeff_le
import Submission.Work.NN.Newton.Bop_eq_identity
import Submission.Work.NN.Newton.exists_pushforward_structure
import Submission.Work.NN.Newton.mNorm_Aop_le
import Submission.Work.NN.Newton.holderNorm_comp_clm_apply_le

/-! Guidance from the project lead (the requester):

FULL ROUTE: read Submission/Work/NN/Newton/DESIGN.md first (Newton iteration on shrinking polydiscs; your lemma is one node of its DAG). Do NOT use Work.NN.Core.dbar_regularity (it rests on an untrusted axiom) and do not import Core/contDiffOn_of_beltrami_fixedPoint together with Core/holderNorm_fiberPot_of_vanishing (duplicate declarations).

# pushforward_small — guidance

**Setting.** `Φ z = fun l => z l − v l z` on `P_{r(1-δ)}`, where `‖v_l‖_{C^{2,α}} ≤ b ≤ δ/C` and the
residual `E^{(l)}_k := Lcoef A z_l k − ∂̄_k v_l` has `C^{1,α}`-norm `≤ e`.

## Key pointwise identity

Verified by `numeric_pushforward_identity.py`, to `1e-15`. With
`A_lin := (A − Jstd A Jstd)/2 = Jstd A²/2` (from `J² = −1`), and for real-linear `h`:

```
(dΦ ∘ J − Jstd ∘ dΦ) h = A_lin h − Σ_k (A_lin e_k)·conj(h_k) − 2i Σ_k E_k·conj(h_k) − Dv(A h).
```

The `ℂ`-antilinear part of `A` cancels against `2 Jstd M`, where `M h = Σ_k ∂̄_k v·conj h_k`.

## Steps

1. **Injectivity.** `‖Dv‖ ≤ n b < 1/2` on the convex `P_{r(1-δ)}`, so
   `‖Φx − Φy − (x − y)‖ ≤ ½‖x − y‖` (mean value).
2. **Image.** For `ζ ∈ P_{r(1-2δ)}`, the map `z ↦ ζ + v(z)` maps the closed polydisc of radius
   `r(1-δ) − η` into itself (`sup|v| ≤ b < rδ − η`) and is a contraction. Its fixed point lies in
   the open `P_{r(1-δ)}` (Mathlib `ContractingWith.fixedPoint` on a complete closed subset).
3. **Inverse.**
   * `Ψ := Φ⁻¹` on `P_{r(1-2δ)}`. It is smooth: use `HasStrictFDerivAt.to_localInverse` /
     `ContDiffAt.to_localInverse`, with local inverses agreeing with the global one by
     injectivity.
   * `DΨ = (1 − Dv)^{-1}∘Ψ`, so `‖DΨ‖ ≤ 2` and `[DΨ]_α ≤ C b`.
4. **Definition.** `A' ζ := (dΦ(Ψζ) ∘ J(Ψζ) ∘ dΦ(Ψζ)^{-1}) − Jstd`. This gives almost complexity
   and the intertwining directly.
5. **Bound.**
   * The `C^{1,α}(P_{r(1-δ)})`-norm of `z ↦ [identity above](z) ∘ dΦ(z)^{-1}` is at most
     `C(a² + e + a b)`. Use Hölder products (`holderNorm_mul_le`) and a Neumann series for
     `(1 − Dv)^{-1}` in `C^{1,α}` (coefficientwise).
   * Compose with `Ψ`: `Work.NN.Final.holderNorm_one_comp_le` with `L = 2`. It needs `hlip`, a
     global Lipschitz bound on `P_{r(1-2δ)}`, which holds since the polydisc is convex.

## Traps

* `holderNorm` is for `ℂ`-valued functions: work with coefficients `z ↦ A z w j`, for `w` in the
  real basis `{e_k, i e_k}` (both of sup-norm `1`), then pass to general `‖w‖ ≤ 1` by linearity
  (`‖w‖ ≤ 1` means `|Re w_k|, |Im w_k| ≤ 1`).
* No `δ`-dependence may enter the constant `C`. All norms are on sets of diameter `≤ 8`, and the
  Lipschitz constant comes from convexity, not from `δ`.
-/

namespace Work.NN.Newton

open scoped ContDiff

/-- **Push-forward of a nearly standard structure by a near-identity map (Hölder calculus).**

Let `J = Jstd + A` be smooth and almost complex on `P_r` with `C^{1,α}`-size `a ≤ 1`, and let `v`
be smooth on `P_{r(1-δ)}` with `‖v_l‖_{C^{2,α}} ≤ b ≤ δ/C` and with residual
`‖∂̄_k v_l - Lcoef A z_l k‖_{C^{1,α}} ≤ e`.  Then `Φ(z) = z - v(z)` is injective on `P_{r(1-δ)}`,
its image contains `P_{r(1-2δ)}`, and the push-forward `J' = Jstd + A'` (defined by
`dΦ ∘ J = J'(Φ) ∘ dΦ`) is smooth and almost complex on `P_{r(1-2δ)}` with
`‖A'‖_{C^{1,α}} ≤ C (a² + e + a b)`.

The pointwise identity behind the bound (checked numerically): with `M h = Σ_k ∂̄_k v · conj h_k`,
`dΦ J - Jstd dΦ = A_lin - Σ_k (A_lin e_k) conj h_k - 2 i Σ_k E_k conj h_k - Dv A`, where
`E_k = Lcoef A z_· k - ∂̄_k v` and `A_lin = Jstd A² / 2` is the `ℂ`-linear part of `A`. -/
theorem pushforward_small {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ r δ : ℝ, 1 ≤ r → r ≤ 4 → 0 < δ → δ ≤ 1 / 8 →
      ∀ A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n,
        (∀ m : ℕ, ContDiffOn ℝ m A
          (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r))) →
        (∀ z, z ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r) →
          ∀ v : Work.NN.Core.Cn n,
            (Work.NN.Core.JstdCn n + A) z ((Work.NN.Core.JstdCn n + A) z v) = -v) →
        ∀ a b e : ℝ, 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ δ / C → 0 ≤ e →
        (∀ w : Work.NN.Core.Cn n, ‖w‖ ≤ 1 → ∀ j : Fin n,
          Work.CR.Flat.holderNorm 1 α (fun z => A z w j)
            (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r))
            ≤ ENNReal.ofReal a) →
        ∀ v : Fin n → Work.NN.Core.Cn n → ℂ,
        (∀ l, ∀ m : ℕ, ContDiffOn ℝ m (v l)
          (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ)))) →
        (∀ l, Work.CR.Flat.holderNorm 2 α (v l)
          (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ)))
            ≤ ENNReal.ofReal b) →
        (∀ l k, Work.CR.Flat.holderNorm 1 α
          (fun z => Work.CR.Flat.dbarCoord k (v l) z - Work.NN.Core.Lcoef A (fun y => y l) k z)
          (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ)))
            ≤ ENNReal.ofReal e) →
        Set.InjOn (fun z : Work.NN.Core.Cn n => fun l => z l - v l z)
            (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ))) ∧
        Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - 2 * δ))
          ⊆ (fun z : Work.NN.Core.Cn n => fun l => z l - v l z) ''
              Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ)) ∧
        ∃ A' : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n,
          (∀ m : ℕ, ContDiffOn ℝ m A'
            (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - 2 * δ)))) ∧
          (∀ z, z ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ)) →
            (fun l => z l - v l z) ∈
              Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - 2 * δ)) →
            ∀ h : Work.NN.Core.Cn n,
              fderiv ℝ (fun y : Work.NN.Core.Cn n => fun l => y l - v l y) z
                  ((Work.NN.Core.JstdCn n + A) z h)
                = (Work.NN.Core.JstdCn n + A') (fun l => z l - v l z)
                    (fderiv ℝ (fun y : Work.NN.Core.Cn n => fun l => y l - v l y) z h)) ∧
          (∀ ζ, ζ ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - 2 * δ)) →
            ∀ w : Work.NN.Core.Cn n,
              (Work.NN.Core.JstdCn n + A') ζ ((Work.NN.Core.JstdCn n + A') ζ w) = -w) ∧
          (∀ w : Work.NN.Core.Cn n, ‖w‖ ≤ 1 → ∀ j : Fin n,
            Work.CR.Flat.holderNorm 1 α (fun ζ => A' ζ w j)
              (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - 2 * δ)))
              ≤ ENNReal.ofReal (C * (a ^ 2 + e + a * b))) := by
  classical
  -- The constant: large enough that `b ≤ δ/C` forces `b ≤ 1/16` and `b ≤ rδ/4`, and
  -- `C ≥ (5 + 2^{1+α})·8·K·(2n)` so that the final bound holds with `K = 2^40 (n+1)^16`.
  set Kc : ℝ := (2 : ℝ) ^ 40 * ((n : ℝ) + 1) ^ 16 with hKc
  set C : ℝ := max 128 (((5 + 2 ^ (1 + α)) * 8 * Kc * (2 * (n : ℝ))) + 1) with hC
  refine ⟨C, ?_, ?_⟩
  · rw [hC]; exact lt_max_of_lt_left (by norm_num)
  · intro r δ hr1 hr4 hδ0 hδ8 A hA hAC a b e ha0 ha1 hb0 hbC he0 haA v hv hvb hve
    have hCpos : 0 < C := by rw [hC]; exact lt_max_of_lt_left (by norm_num)
    have hC128 : (128 : ℝ) ≤ C := by rw [hC]; exact le_max_left _ _
    have hKle : ((5 + 2 ^ (1 + α)) * 8 * Kc * (2 * (n : ℝ))) ≤ C := by
      rw [hC]; linarith [le_max_right (128 : ℝ) ((5 + 2 ^ (1 + α)) * 8 * Kc * (2 * (n : ℝ)) + 1)]
    have hbC' : b * C ≤ δ := by
      have h2 := mul_le_mul_of_nonneg_right hbC (le_of_lt hCpos)
      rwa [div_mul_cancel₀ δ (ne_of_gt hCpos)] at h2
    have hb16 : b ≤ 1 / 16 := by
      rw [le_div_iff₀ (by norm_num : (0:ℝ) < 16)]
      nlinarith [hbC', hδ8, hC128, hb0]
    have hbδ : b ≤ r * δ / 4 := by
      rw [le_div_iff₀ (by norm_num : (0:ℝ) < 4)]
      nlinarith [hbC', hr1, hδ0, hC128, hb0]
    obtain ⟨Ψ, hΨsm, hΨleft, hΨright, hΨmem, hΨlip, hΨder, hΨderα, A', hA'eq, hA'sm, hA'int,
      hA'ac⟩ :=
      exists_pushforward_structure (b := b) (n := n) hn hα0 hα1 hr1 hr4 hδ0 hδ8 A hA hAC hv hb0 hvb hbδ hb16
    refine ⟨?_, ?_, A', hA'sm, ?_, ?_, ?_⟩
    · -- injectivity of `Φ v` on `P_{r(1-δ)}`
      set Ω : Set (Work.NN.Core.Cn n) := Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ)) with hΩ
      have hΩope : IsOpen Ω := Work.CR.Flat.isOpen_polydisc 0 _
      have hconv : Convex ℝ Ω := convex_Pd n _
      have hvdiff : ∀ z ∈ Ω, ∀ l, DifferentiableAt ℝ (v l) z := by
        intro z hz l
        exact ((hv l 1).contDiffAt (hΩope.mem_nhds hz)).differentiableAt (by norm_num)
      have hVfd : ∀ z ∈ Ω,
          fderiv ℝ (fun y : Work.NN.Core.Cn n => fun l => v l y) z = DvCLM v z := by
        intro z hz
        rw [DvCLM]
        exact fderiv_pi (fun l => hvdiff z hz l)
      have hbnd : ∀ z ∈ Ω,
          ‖fderiv ℝ (fun y : Work.NN.Core.Cn n => fun l => v l y) z‖ ≤ b := by
        intro z hz
        rw [hVfd z hz, ContinuousLinearMap.opNorm_le_iff hb0]
        intro h
        rw [DvCLM_apply]
        refine (pi_norm_le_iff_of_nonneg (mul_nonneg hb0 (norm_nonneg h))).mpr fun l => ?_
        have hl : ‖fderiv ℝ (v l) z‖ ≤ b := by
          have h2 : ‖iteratedFDerivWithin ℝ 1 (v l) Ω z‖ = ‖fderiv ℝ (v l) z‖ := by
            rw [iteratedFDerivWithin_of_isOpen 1 hΩope hz, norm_iteratedFDeriv_one]
          have h3 : ENNReal.ofReal ‖fderiv ℝ (v l) z‖ ≤ ENNReal.ofReal b := by
            rw [← h2]
            exact (Work.CR.Flat.le_iterDerivNorm 1 (v l) _ hz).trans
              ((Work.CR.Flat.iterDerivNorm_le_holderNorm 2 α (v l) _ (by norm_num)).trans
                (hvb l))
          exact (ENNReal.ofReal_le_ofReal_iff hb0).mp h3
        calc ‖fderiv ℝ (v l) z h‖ ≤ ‖fderiv ℝ (v l) z‖ * ‖h‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ b * ‖h‖ := mul_le_mul_of_nonneg_right hl (norm_nonneg h)
      have hsplit : ∀ x y : Work.NN.Core.Cn n,
          Phi v x - Phi v y = (x - y) - ((fun y : Work.NN.Core.Cn n => fun l => v l y) x
            - (fun y : Work.NN.Core.Cn n => fun l => v l y) y) := by
        intro x y
        ext l
        simp only [Pi.sub_apply, Phi_apply]
        ring
      intro x hx y hy hxy
      have hmvt : ‖(fun y : Work.NN.Core.Cn n => fun l => v l y) x
          - (fun y : Work.NN.Core.Cn n => fun l => v l y) y‖ ≤ b * ‖x - y‖ := by
        have h := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
          (fun z hz => differentiableAt_pi.mpr (hvdiff z hz)) hbnd hconv hy hx
        simpa only [norm_sub_rev] using h
      have hkey : x - y = (fun y : Work.NN.Core.Cn n => fun l => v l y) x
          - (fun y : Work.NN.Core.Cn n => fun l => v l y) y := by
        have h0 : Phi v x - Phi v y = 0 := sub_eq_zero.mpr hxy
        rw [hsplit x y] at h0
        exact sub_eq_zero.mp h0
      have hnorm : ‖x - y‖ ≤ b * ‖x - y‖ :=
        calc ‖x - y‖ = ‖(fun y : Work.NN.Core.Cn n => fun l => v l y) x
                - (fun y : Work.NN.Core.Cn n => fun l => v l y) y‖ := by rw [hkey]
          _ ≤ b * ‖x - y‖ := hmvt
      have hb1 : b < 1 := by linarith [hb16]
      have h0 : x - y = 0 := by
        by_contra hc
        have hpos : 0 < ‖x - y‖ := norm_pos_iff.mpr hc
        nlinarith
      exact sub_eq_zero.mp h0
    · -- the image contains `P_{r(1-2δ)}`
      intro ζ hζ
      exact ⟨Ψ ζ, hΨmem ζ hζ, hΨleft ζ hζ⟩
    · -- intertwining
      intro z hz hz' h
      exact hA'int z hz hz' h
    · -- almost complexity
      intro ζ hζ w
      exact hA'ac ζ hζ w
    · -- the `C^{1,α}` bound on the push-forward
      set Ω : Set (Work.NN.Core.Cn n) :=
        Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ)) with hΩ
      set Λ : Set (Work.NN.Core.Cn n) :=
        Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - 2 * δ)) with hΛ
      have hΩope : IsOpen Ω := Work.CR.Flat.isOpen_polydisc 0 _
      have hΛope : IsOpen Λ := Work.CR.Flat.isOpen_polydisc 0 _
      have hRpos : (0 : ℝ) < r * (1 - δ) := by
        refine mul_pos (by linarith) ?_
        linarith
      have hS : 0 ≤ a ^ 2 + e + a * b := by
        nlinarith [sq_nonneg a, mul_nonneg ha0 hb0, he0]
      have hKcpos : 0 < Kc := by rw [hKc]; positivity
      have hK0 : 0 ≤ Kc * (a ^ 2 + e + a * b) := mul_nonneg (le_of_lt hKcpos) hS
      -- smoothness of the pushed-forward perturbation on `Ω`
      have hunitAop : ∀ z ∈ Ω, IsUnit (1 - DvCLM v z) := by
        intro z hz
        have hbnd : ‖DvCLM v z‖ ≤ b := (DvCLM_data_le hα0 hRpos hv hb0 hvb).2.1 z hz
        refine IsUnit.one_sub_of_norm_lt_one (lt_of_le_of_lt hbnd ?_)
        linarith [hb16]
      have hle : r * (1 - δ) ≤ r := by
        have h : r * (1 - δ) = r - r * δ := by ring
        rw [h]
        have hpos : 0 < r * δ := mul_pos (by linarith) hδ0
        linarith
      have hAop_sm : ∀ m : ℕ, ContDiffOn ℝ m (fun z => Aop A v z) Ω :=
        contDiffOn_Aop (fun m => (hA m).mono (Pd_mono hle)) hv hunitAop
      -- the `mNorm` bound on `Ω`
      have hM' : Work.NN.Newton.mNorm 1 α (fun z => Aop A v z) Ω
          ≤ ENNReal.ofReal (Kc * (a ^ 2 + e + a * b)) := by
        have h := mNorm_Aop_le (n := n) hα0 hα1 hr1 hr4 hδ0 hδ8 A hA hAC hv
          ha0 ha1 hb0 he0 haA hvb hve hbδ hb16
        rw [hΩ, hKc]
        exact h
      -- the `C^{1,α}` data of `Ψ`
      have hΨsmΛ : ∀ m : ℕ, ContDiffOn ℝ m Ψ Λ := by rw [hΛ]; exact hΨsm
      have hΨmemΛ : ∀ x ∈ Λ, Ψ x ∈ Ω := by rw [hΩ, hΛ]; exact hΨmem
      have hΨlipΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, ‖Ψ x - Ψ y‖ ≤ 2 * ‖x - y‖ := by
        rw [hΛ]; exact hΨlip
      have hΨderΛ : ∀ x ∈ Λ, ‖fderiv ℝ Ψ x‖ ≤ 2 := by rw [hΛ]; exact hΨder
      have hΨderαΛ : ∀ x ∈ Λ, ∀ y ∈ Λ,
          ‖fderiv ℝ Ψ x - fderiv ℝ Ψ y‖ ≤ 2 * ‖x - y‖ ^ α := by
        rw [hΛ]
        intro x hx y hy
        refine le_trans (hΨderα x hx y hy) ?_
        have hnn : (0 : ℝ) ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
        linarith
      intro w hw j
      have hstep := holderNorm_comp_clm_apply_le (n := n) (j := j) hα0 hΩope hΛope hAop_sm hΨsmΛ
        hΨmemΛ hΨlipΛ hΨderΛ hΨderαΛ hM' hK0 hw
      have heq : Work.CR.Flat.holderNorm 1 α (fun ζ => A' ζ w j) Λ
          = Work.CR.Flat.holderNorm 1 α (fun ζ => (Aop A v (Ψ ζ) w) j) Λ :=
        holderNorm_congr (fun ζ hζ => by rw [hA'eq ζ hζ])
      rw [heq]
      refine hstep.trans (ENNReal.ofReal_le_ofReal ?_)
      -- the final arithmetic: `(5 + 2^{1+α}) · 8 · Kc · n ≤ C`
      have h2n : (n : ℝ) ≤ 2 * (n : ℝ) := by
        have h0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      have hP0 : 0 ≤ (5 + 2 ^ (1 + α)) * 8 * Kc := by
        have h2a : (0 : ℝ) < 2 ^ (1 + α) := Real.rpow_pos_of_pos (by norm_num) (1 + α)
        positivity
      have hfactor : (5 + 2 ^ (1 + α)) * 8 * Kc * (n : ℝ) ≤ C := by
        calc (5 + 2 ^ (1 + α)) * 8 * Kc * (n : ℝ)
            = ((5 + 2 ^ (1 + α)) * 8 * Kc) * (n : ℝ) := by ring
          _ ≤ ((5 + 2 ^ (1 + α)) * 8 * Kc) * (2 * (n : ℝ)) :=
              mul_le_mul_of_nonneg_left h2n hP0
          _ = (5 + 2 ^ (1 + α)) * 8 * Kc * (2 * (n : ℝ)) := by ring
          _ ≤ C := hKle
      have harith : (5 + 2 ^ (1 + α)) * 8 * (Kc * (a ^ 2 + e + a * b)) * (n : ℝ)
          ≤ C * (a ^ 2 + e + a * b) := by
        have h1 : (5 + 2 ^ (1 + α)) * 8 * (Kc * (a ^ 2 + e + a * b)) * (n : ℝ)
            = ((5 + 2 ^ (1 + α)) * 8 * Kc * (n : ℝ)) * (a ^ 2 + e + a * b) := by ring
        rw [h1]
        exact mul_le_mul_of_nonneg_right hfactor hS
      exact harith

end Work.NN.Newton
