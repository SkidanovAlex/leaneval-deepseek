import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.NN.Core.bijective_add_of_norm_comp_lt_one
import Submission.Work.NN.Final.Defs
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.NN.Newton.newtonCorrection
import Submission.Work.NN.Newton.pushforward_small
import Submission.Work.NN.Newton.integrable_pushforward
import Submission.Work.NN.Newton.newtonStepConsts
import Submission.Work.NN.Newton.phiNormBounds

/-! Guidance from the project lead (the requester):

FULL ROUTE: read Submission/Work/NN/Newton/DESIGN.md first. Your inputs are the sibling lemmas in depends_on (being proved in parallel; build against their statements). Do NOT use Work.NN.Core.dbar_regularity (rests on sorryAx).

# newton_step — guidance

Assembly of `newtonCorrection`, `pushforward_small` and `integrable_pushforward`.

1. Get `C₄, N₄` from `newtonCorrection`, `C₅` from `pushforward_small`.
   * Set `N := N₄ + 1` and `C` large, so that `a ≤ δ^N/C` implies `a ≤ 1` and
     `b := C₄δ^{-N₄}a ≤ δ/C₅`.
2. `newtonCorrection` at `(r, δ)` gives `v`. Set `Φ := fun z l => z l − v l z` (so `Φ z − z = −v z`).
3. `pushforward_small` with `b` and `e := C₄δ^{-N₄}a²` gives injectivity, the image, `A'`, the
   intertwining, `J'² = −1`, and `‖A'‖ ≤ C₅(a² + e + a b) ≤ Cδ^{-N}a²`.
4. `integrable_pushforward` with `Ω = P_{r(1-δ)}`, `Ω' = P_{r(1-2δ)}`, `J = Jstd + A`, `J' = Jstd + A'`.
   * The hypothesis restricts from `P_r` to `Ω`.
   * `hbij` from `‖Dv‖ < 1` (`Work.NN.Core.bijective_add_of_norm_comp_lt_one`).
   * `hpush` from step 3, since `Φ z ∈ Ω'` is part of its hypothesis.
5. **`‖Φ z − z‖` and `‖fderiv Φ z − id‖`.**
   * The sup norm on `Cn n` means `‖(x_l)_l‖ = max_l |x_l|`, and the operator norm of
     `h ↦ (Dv_l h)_l` is `max_l ‖Dv_l‖`.
   * Each is bounded by `holderNorm 2 α (v l)`, via `Work.CR.Flat.norm_apply_le_holderNorm` and
     `iterDerivNorm_le_holderNorm` (on an open set, `iteratedFDerivWithin 1 = fderiv`).
   * The norm of `fderiv` of the tuple map is bounded via `ContinuousLinearMap.opNorm_le_bound` and
     the pi structure.
6. Smoothness of `Φ`: `contDiffOn_pi` of `id − v l`.
-/

namespace Work.NN.Newton

open scoped ContDiff

/-- **One Newton step for Newlander–Nirenberg on concentric polydiscs (quadratic gain).**

Let `J = Jstd + A` be smooth, almost complex and integrable on the polydisc `P_r` (`1 ≤ r ≤ 4`),
with `C^{1,α}`-size `a ≤ δ^N / C`.  Then there is a smooth map `Φ` (namely `z - v(z)` with `v` from
`newtonCorrection`), injective on `P_{r(1-δ)}` with image containing `P_{r(1-2δ)}`, `C¹`-close to
the identity (`‖Φ - id‖, ‖dΦ - 1‖ ≤ (C/δ^N) a`), such that the push-forward structure
`J' = Jstd + A'` is smooth, almost complex and integrable on `P_{r(1-2δ)}` and has `C^{1,α}`-size
at most `(C/δ^N) a²`. -/
theorem newton_step {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ r δ : ℝ, 1 ≤ r → r ≤ 4 → 0 < δ → δ ≤ 1 / 8 →
      ∀ A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n,
        (∀ m : ℕ, ContDiffOn ℝ m A
          (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r))) →
        (∀ z, z ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r) →
          ∀ v : Work.NN.Core.Cn n,
            (Work.NN.Core.JstdCn n + A) z ((Work.NN.Core.JstdCn n + A) z v) = -v) →
        (∀ u : Work.NN.Core.Cn n → ℂ, (∀ k : ℕ, ContDiff ℝ k u) →
          ∀ z, z ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r) →
            ∀ V W : Work.NN.Core.Cn n,
              Work.NN.Final.proj02 (Work.NN.Core.JstdCn n + A)
                (fun z' => Work.NN.Final.dOne
                  (fun z'' => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) u z'') z')
                z V W = 0) →
        ∀ a : ℝ, 0 ≤ a → a ≤ δ ^ N / C →
        (∀ w : Work.NN.Core.Cn n, ‖w‖ ≤ 1 → ∀ j : Fin n,
          Work.CR.Flat.holderNorm 1 α (fun z => A z w j)
            (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r))
            ≤ ENNReal.ofReal a) →
        ∃ Φ : Work.NN.Core.Cn n → Work.NN.Core.Cn n,
          (∀ m : ℕ, ContDiffOn ℝ m Φ
            (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ)))) ∧
          Set.InjOn Φ (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ))) ∧
          Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - 2 * δ))
            ⊆ Φ '' Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ)) ∧
          (∀ z, z ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ)) →
            ‖Φ z - z‖ ≤ C / δ ^ N * a) ∧
          (∀ z, z ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ)) →
            ‖fderiv ℝ Φ z - ContinuousLinearMap.id ℝ (Work.NN.Core.Cn n)‖ ≤ C / δ ^ N * a) ∧
          ∃ A' : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n,
            (∀ m : ℕ, ContDiffOn ℝ m A'
              (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - 2 * δ)))) ∧
            (∀ z, z ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - δ)) →
              Φ z ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - 2 * δ)) →
              ∀ h : Work.NN.Core.Cn n,
                fderiv ℝ Φ z ((Work.NN.Core.JstdCn n + A) z h)
                  = (Work.NN.Core.JstdCn n + A') (Φ z) (fderiv ℝ Φ z h)) ∧
            (∀ ζ, ζ ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - 2 * δ)) →
              ∀ w : Work.NN.Core.Cn n,
                (Work.NN.Core.JstdCn n + A') ζ ((Work.NN.Core.JstdCn n + A') ζ w) = -w) ∧
            (∀ u : Work.NN.Core.Cn n → ℂ, (∀ k : ℕ, ContDiff ℝ k u) →
              ∀ ζ, ζ ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - 2 * δ)) →
                ∀ V W : Work.NN.Core.Cn n,
                  Work.NN.Final.proj02 (Work.NN.Core.JstdCn n + A')
                    (fun z' => Work.NN.Final.dOne
                      (fun z'' => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A') u z'') z')
                    ζ V W = 0) ∧
            (∀ w : Work.NN.Core.Cn n, ‖w‖ ≤ 1 → ∀ j : Fin n,
              Work.CR.Flat.holderNorm 1 α (fun ζ => A' ζ w j)
                (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ => r * (1 - 2 * δ)))
                ≤ ENNReal.ofReal (C / δ ^ N * a ^ 2)) := by
  obtain ⟨C₄, hC₄, N₄, hcorr⟩ := newtonCorrection hn hα0 hα1
  obtain ⟨C₅, hC₅, hpf⟩ := pushforward_small hn hα0 hα1
  obtain ⟨C, hCpos, hconst⟩ := newtonStepConsts hC₄ hC₅ N₄
  refine ⟨C, hCpos, N₄ + 1, ?_⟩
  intro r δ hr1 hr4 hδ0 hδ8 A hA_sm hA_ac hA_int a ha0 ha_le hA_holder
  have hΩP : Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ : Fin n => r * (1 - δ))
      ⊆ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ : Fin n => r) :=
    Work.CR.Flat.polydisc_mono (fun j => by nlinarith)
  obtain ⟨ha1, hb0, hbδ, hb1, hbrel, he0, hc₅⟩ :=
    hconst r δ a hr1 hr4 hδ0 hδ8 ha0 ha_le
  obtain ⟨v, hv_sm, hv_norm, hv_res⟩ :=
    hcorr r δ hr1 hr4 hδ0 hδ8 A hA_sm hA_ac hA_int a ha0 ha1 hA_holder
  obtain ⟨hinj, himg, A', hA'sm, hA'push, hA'ac, hA'norm⟩ :=
    hpf r δ hr1 hr4 hδ0 hδ8 A hA_sm hA_ac a (C₄ / δ ^ N₄ * a) (C₄ / δ ^ N₄ * a ^ 2)
      ha0 ha1 hb0 hbδ he0 hA_holder v hv_sm hv_norm hv_res
  have hΦsm : ∀ m : ℕ, ContDiffOn ℝ m
      (fun z : Work.NN.Core.Cn n => fun l : Fin n => z l - v l z)
      (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ : Fin n => r * (1 - δ))) := by
    intro m
    rw [contDiffOn_pi]
    intro l
    exact ((ContinuousLinearMap.proj l : Work.NN.Core.Cn n →L[ℝ] ℂ).contDiff.contDiffOn).sub
      (hv_sm l m)
  have hΦb := phiNormBounds
    (Work.CR.Flat.isOpen_polydisc (0 : Work.NN.Core.Cn n) (fun _ : Fin n => r * (1 - δ)))
    hb0 hv_norm (fun l => hv_sm l 1)
  have hbij : ∀ z ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ : Fin n => r * (1 - δ)),
      Function.Bijective (fderiv ℝ (fun w : Work.NN.Core.Cn n => fun l : Fin n => w l - v l w) z) := by
    intro z hz
    have hlt : ‖fderiv ℝ (fun w : Work.NN.Core.Cn n => fun l : Fin n => w l - v l w) z
        - ContinuousLinearMap.id ℝ (Work.NN.Core.Cn n)‖ < 1 :=
      lt_of_le_of_lt (hΦb.2 z hz) hb1
    have h := Work.NN.Core.bijective_add_of_norm_comp_lt_one
      (ContinuousLinearMap.id ℝ (Work.NN.Core.Cn n))
      (ContinuousLinearMap.id ℝ (Work.NN.Core.Cn n))
      rfl rfl
      (fderiv ℝ (fun w : Work.NN.Core.Cn n => fun l : Fin n => w l - v l w) z
        - ContinuousLinearMap.id ℝ (Work.NN.Core.Cn n))
      (by rw [ContinuousLinearMap.id_comp]; exact hlt)
    have heq : (ContinuousLinearMap.id ℝ (Work.NN.Core.Cn n))
        + (fderiv ℝ (fun w : Work.NN.Core.Cn n => fun l : Fin n => w l - v l w) z
          - ContinuousLinearMap.id ℝ (Work.NN.Core.Cn n))
        = fderiv ℝ (fun w : Work.NN.Core.Cn n => fun l : Fin n => w l - v l w) z := by abel
    rwa [heq] at h
  have hJsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.NN.Core.JstdCn n + A)
      (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ : Fin n => r * (1 - δ))) := by
    intro m
    exact ((contDiffOn_const (c := Complex.I • (1 : Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n))).add
      (hA_sm m)).mono hΩP
  have hJ'sm : ∀ m : ℕ, ContDiffOn ℝ m (Work.NN.Core.JstdCn n + A')
      (Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ : Fin n => r * (1 - 2 * δ))) := by
    intro m
    exact (contDiffOn_const (c := Complex.I • (1 : Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n))).add
      (hA'sm m)
  have hint : ∀ (u : Work.NN.Core.Cn n → ℂ), (∀ k : ℕ, ContDiff ℝ k u) →
      ∀ z ∈ Work.CR.Flat.polydisc (0 : Work.NN.Core.Cn n) (fun _ : Fin n => r * (1 - δ)),
        ∀ V W : Work.NN.Core.Cn n,
          Work.NN.Final.proj02 (Work.NN.Core.JstdCn n + A)
            (fun z' => Work.NN.Final.dOne
              (fun z'' => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) u z'') z') z V W = 0 :=
    fun u hu z hz V W => hA_int u hu z (hΩP hz) V W
  have hInt := integrable_pushforward
    (Work.CR.Flat.isOpen_polydisc (0 : Work.NN.Core.Cn n) (fun _ : Fin n => r * (1 - δ)))
    (Work.CR.Flat.isOpen_polydisc (0 : Work.NN.Core.Cn n) (fun _ : Fin n => r * (1 - 2 * δ)))
    hJsm hJ'sm hΦsm hbij himg hA'push hint
  refine ⟨(fun z : Work.NN.Core.Cn n => fun l : Fin n => z l - v l z), hΦsm, hinj, himg, ?_, ?_,
    A', hA'sm, hA'push, hA'ac, hInt, ?_⟩
  · intro z hz
    exact le_trans (hΦb.1 z hz) hbrel
  · intro z hz
    exact le_trans (hΦb.2 z hz) hbrel
  · intro w hw j
    exact le_trans (hA'norm w hw j) (ENNReal.ofReal_le_ofReal hc₅)


end Work.NN.Newton
