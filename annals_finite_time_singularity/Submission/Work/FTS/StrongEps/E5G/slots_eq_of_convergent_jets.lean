import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.E5G.Defs
import Submission.Work.FTS.StrongEps.E5Aux3.LimDeriv
import Submission.Work.FTS.StrongEps.E5Aux3.contDiffOn_two_of_jetLim
import Submission.Work.FTS.StrongEps.LocUnif.tendstoUniformlyOn_of_pointwise_of_equicont
import Submission.Work.FTS.StrongEps.E5G.equicont_of_holder
import Submission.Work.FTS.StrongEps.E5G.tendstoUniformlyOn_of_pointwise_of_holder
import Submission.Work.FTS.StrongEps.E5G.fderiv_uncurry_mixed_eq_clmPair
import Submission.Work.FTS.StrongEps.E5G.hasFDerivAt_of_slot_tlu

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Filter Set

namespace Work.FTS.StrongEps.E5G

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The jets of a limit along convergent jets

Let `V n` be smooth on the open quadrant `Q0 = (0,∞) × (0,π/2)`, converging pointwise to `R`, and
suppose that the weighted jets `D_z^jD_θ^i (V n)` (`j + i ≤ 3`) converge pointwise to `Φ j i`, that
the jets are equi-Hölder-`1/2` on compact subsets of `Q0`, and uniformly bounded there.  The claim
is that the jets of the limit `R` are exactly the limits: `D_z^jD_θ^i R = Φ j i` on `Q0` for
`j + i ≤ 3`.

The proof has two layers.

* **Uniform convergence.**  Equi-Hölder-`1/2` plus pointwise convergence on a compact `K` gives
  *uniform* convergence on `K` (the convergence half of Arzelà–Ascoli), hence locally uniform
  convergence on `Q0` for every jet of order `≤ 3`.
* **Differentiation of the limit.**  Locally uniform convergence of `f n := D_z^jD_θ^i (V n)`
  together with locally uniform convergence of the Fréchet derivatives
  `fderiv ℝ (uncurry (f n))` (the latter is read off from the *next* jets: the `z`-partial of a jet
  is the next `z`-jet divided by `z`, the `θ`-partial the next `θ`-jet divided by `sin 2θ`) lets
  Mathlib's `hasFDerivAt_of_tendstoLocallyUniformlyOn` differentiate the limit.  Inducting over
  `j + i ≤ 3` gives the result.
-/

/-- The `(j,i)`-jet `D_z^j D_θ^i u` of a curried function, as a function on `ℝ × ℝ`. -/
private def slot (j i : ℕ) (u : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => Work.Spaces.mixed j i u p.1 p.2

/-- The pointwise limit of the `(j,i)`-jets, as a function on `ℝ × ℝ`. -/
private def slotLim (Φ : ℕ → ℕ → ℝ → ℝ → ℝ) (j i : ℕ) : ℝ × ℝ → ℝ :=
  fun p => Φ j i p.1 p.2

/-! ## The successor identity for the `θ`-jets -/

/-- `D_θ^{i+1} u = sin 2θ · ∂_θ (D_θ^i u)`. -/
private theorem mixed_succ_th (u : ℝ → ℝ → ℝ) (i : ℕ) (z θ : ℝ) :
    Work.Spaces.mixed 0 (i + 1) u z θ
      = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.mixed 0 i u) z θ := by
  simp only [Work.Spaces.mixed, Work.Spaces.DthIter_succ, Work.Spaces.Dth,
    Work.Spaces.DzIter_zero]

/-! ## Step 1: locally uniform convergence of the jets -/

/-- **Locally uniform convergence of every jet of order `≤ 3`.** -/
private theorem slot_tlu_of_jets {V : ℕ → ℝ → ℝ → ℝ} {Φ : ℕ → ℕ → ℝ → ℝ → ℝ}
    (hconv : ∀ (j i : ℕ), j + i ≤ 3 → ∀ q ∈ Work.FTS.EllipticEst.Q0,
      Filter.Tendsto (fun n => Work.Spaces.mixed j i (V n) q.1 q.2) Filter.atTop
        (nhds (Φ j i q.1 q.2)))
    (hequi : ∀ (j i : ℕ), j + i ≤ 3 → ∀ K : Set (ℝ × ℝ), IsCompact K →
      K ⊆ Work.FTS.EllipticEst.Q0 → ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ p ∈ K, ∀ q ∈ K,
        |Work.Spaces.mixed j i (V n) p.1 p.2 - Work.Spaces.mixed j i (V n) q.1 q.2|
          ≤ C * dist p q ^ (1 / 2 : ℝ)) :
    ∀ (j i : ℕ), j + i ≤ 3 →
      TendstoLocallyUniformlyOn (fun n : ℕ => slot j i (V n)) (slotLim Φ j i) Filter.atTop
        Work.FTS.EllipticEst.Q0 := by
  intro j i hji
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact Work.FTS.EllipticEst.isOpen_Q0]
  intro K hKQ hK
  obtain ⟨C, hC, hCd⟩ := hequi j i hji K hK hKQ
  exact tendstoUniformlyOn_of_pointwise_of_holder hK (fun p hp => hconv j i hji p (hKQ hp))
    (equicont_of_holder hC hCd)

/-! ## Step 2: the jets of the limit

The locally uniform convergence of the jets (`slot_tlu_of_jets`) is upgraded to the jets of the
limit by induction on `j + i`: the `z`-partial of a jet is the next `z`-jet divided by `z`, the
`θ`-partial the next `θ`-jet divided by `sin 2θ` (`fderiv_uncurry_mixed_eq_clmPair`), so the
Fréchet derivatives converge locally uniformly and
`hasFDerivAt_of_slot_tlu` differentiates the limit. -/

theorem slots_eq_of_convergent_jets {V : ℕ → Work.FTS.Galerkin.Fn} {R : Work.FTS.Galerkin.Fn}
    {Φ : ℕ → ℕ → Work.FTS.Galerkin.Fn}
    (hsm : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (V n))
    (hR : ∀ q ∈ Work.FTS.EllipticEst.Q0,
      Filter.Tendsto (fun n => V n q.1 q.2) Filter.atTop (nhds (R q.1 q.2)))
    (hconv : ∀ (j i : ℕ), j + i ≤ 3 → ∀ q ∈ Work.FTS.EllipticEst.Q0,
      Filter.Tendsto (fun n => Work.Spaces.mixed j i (V n) q.1 q.2) Filter.atTop
        (nhds (Φ j i q.1 q.2)))
    (hequi : ∀ (j i : ℕ), j + i ≤ 3 → ∀ K : Set (ℝ × ℝ), IsCompact K →
      K ⊆ Work.FTS.EllipticEst.Q0 → ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ p ∈ K, ∀ q ∈ K,
        |Work.Spaces.mixed j i (V n) p.1 p.2 - Work.Spaces.mixed j i (V n) q.1 q.2|
          ≤ C * dist p q ^ (1 / 2 : ℝ))
    (hbnd : ∀ (j i : ℕ), j + i ≤ 3 → ∀ K : Set (ℝ × ℝ), IsCompact K →
      K ⊆ Work.FTS.EllipticEst.Q0 → ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ p ∈ K,
        |Work.Spaces.mixed j i (V n) p.1 p.2| ≤ C) :
    ∀ (j i : ℕ), j + i ≤ 3 → ∀ q ∈ Work.FTS.EllipticEst.Q0,
      Work.Spaces.mixed j i R q.1 q.2 = Φ j i q.1 q.2 := by
  classical
  have hslot : ∀ (j i : ℕ), j + i ≤ 3 →
      TendstoLocallyUniformlyOn (fun n : ℕ => slot j i (V n)) (slotLim Φ j i) Filter.atTop
        Work.FTS.EllipticEst.Q0 :=
    slot_tlu_of_jets (V := fun n => V n) (Φ := fun j i => Φ j i) hconv hequi
  have hcontΦ : ∀ (j i : ℕ), j + i ≤ 3 →
      ContinuousOn (slotLim Φ j i) Work.FTS.EllipticEst.Q0 := fun j i hji =>
    (hslot j i hji).continuousOn
      (Eventually.of_forall fun n => ((hsm n).mixed j i).forall 0 |>.continuousOn).frequently
  have hz0 : ∀ p ∈ Work.FTS.EllipticEst.Q0, p.1 ≠ 0 :=
    fun p hp => ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1
  have hs0 : ∀ p ∈ Work.FTS.EllipticEst.Q0, Real.sin (2 * p.2) ≠ 0 := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))
  have hsin_cont : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2))
      Work.FTS.EllipticEst.Q0 :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
  have hdiffV : ∀ (n j i : ℕ) (p : ℝ × ℝ), p ∈ Work.FTS.EllipticEst.Q0 →
      DifferentiableAt ℝ (Function.uncurry (Work.Spaces.mixed j i (V n))) p :=
    fun n j i p hp => (((hsm n).mixed j i).forall 1).differentiableOn (by norm_num)
      |>.differentiableAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hp)
  -- the `z`-divided and `sin 2θ`-divided jets converge locally uniformly
  have hdivp1 : ∀ (j i : ℕ), (j + 1) + i ≤ 3 →
      TendstoLocallyUniformlyOn
        (fun n : ℕ => fun p : ℝ × ℝ => Work.Spaces.mixed (j + 1) i (V n) p.1 p.2 / p.1)
        (fun p : ℝ × ℝ => Φ (j + 1) i p.1 p.2 / p.1) Filter.atTop Work.FTS.EllipticEst.Q0 :=
    fun j i hji => (hslot (j + 1) i hji).div₀
      (Work.FTS.StrongEps.E5Aux.tlu_const (fun p : ℝ × ℝ => p.1) Work.FTS.EllipticEst.Q0)
      (hcontΦ (j + 1) i hji) continuous_fst.continuousOn (fun p hp => hz0 p hp)
  have hdivsn : ∀ (j i : ℕ), j + (i + 1) ≤ 3 →
      TendstoLocallyUniformlyOn
        (fun n : ℕ => fun p : ℝ × ℝ =>
          Work.Spaces.mixed j (i + 1) (V n) p.1 p.2 / Real.sin (2 * p.2))
        (fun p : ℝ × ℝ => Φ j (i + 1) p.1 p.2 / Real.sin (2 * p.2)) Filter.atTop
        Work.FTS.EllipticEst.Q0 :=
    fun j i hji => (hslot j (i + 1) hji).div₀
      (Work.FTS.StrongEps.E5Aux.tlu_const (fun p : ℝ × ℝ => Real.sin (2 * p.2))
        Work.FTS.EllipticEst.Q0)
      (hcontΦ j (i + 1) hji) hsin_cont (fun p hp => hs0 p hp)
  suffices key : ∀ m : ℕ, ∀ (j i : ℕ), j + i = m → j + i ≤ 3 →
      ∀ q ∈ Work.FTS.EllipticEst.Q0, Work.Spaces.mixed j i R q.1 q.2 = Φ j i q.1 q.2 by
    intro j i hji
    exact key (j + i) j i rfl hji
  intro m
  refine Nat.strong_induction_on m ?_
  intro k ih j i hm hji q hq
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    rcases Nat.eq_zero_or_pos i with hi | hi
    · -- the level-zero case: `V n → R` and `V n → Φ 0 0` pointwise
      subst hi
      have hcv : Filter.Tendsto (fun n : ℕ => V n q.1 q.2) Filter.atTop
          (nhds (Φ 0 0 q.1 q.2)) := by
        simpa [Work.Spaces.mixed] using hconv 0 0 (by norm_num) q hq
      have huniq := tendsto_nhds_unique (hR q hq) hcv
      simpa [Work.Spaces.mixed] using huniq
    · -- `j = 0`, `i ≥ 1`: differentiate the lower jet in `θ`
      obtain ⟨i', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
      have hlow : ∀ r ∈ Work.FTS.EllipticEst.Q0,
          Work.Spaces.mixed 0 i' R r.1 r.2 = Φ 0 i' r.1 r.2 :=
        ih (0 + i') (by omega) 0 i' rfl (by omega)
      have hJet : TendstoLocallyUniformlyOn
          (fun n : ℕ => fderiv ℝ (Function.uncurry (Work.Spaces.mixed 0 i' (V n))))
          (fun p : ℝ × ℝ => Work.FTS.StrongEps.E5Aux.clmPair
            (Φ 1 i' p.1 p.2 / p.1, Φ 0 (i' + 1) p.1 p.2 / Real.sin (2 * p.2)))
          Filter.atTop Work.FTS.EllipticEst.Q0 :=
        (Work.FTS.StrongEps.E5Aux.tendstoLocallyUniformlyOn_clmPair
          (hdivp1 0 i' (by omega)) (hdivsn 0 i' (by omega))).congr
          (fun n => fun p hp => (fderiv_uncurry_mixed_eq_clmPair (hsm n) 0 i' hp).symm)
      have hderiv : HasFDerivAt (Function.uncurry (Work.Spaces.mixed 0 i' R))
          (Work.FTS.StrongEps.E5Aux.clmPair
            (Φ 1 i' q.1 q.2 / q.1, Φ 0 (i' + 1) q.1 q.2 / Real.sin (2 * q.2))) q :=
        hasFDerivAt_of_slot_tlu (W := fun n => Work.Spaces.mixed 0 i' (V n))
          (F := Φ 0 i') (R := Work.Spaces.mixed 0 i' R)
          hq (fun n p hp => hdiffV n 0 i' p hp) (hslot 0 i' (by omega)) hJet
          (fun p hp => hlow p hp)
      have hpth : Work.Spaces.pth (Work.Spaces.mixed 0 i' R) q.1 q.2
          = Φ 0 (i' + 1) q.1 q.2 / Real.sin (2 * q.2) := by
        rw [Work.Spaces.pth_eq_fderiv hderiv.differentiableAt, hderiv.fderiv]
        simp
      rw [show Work.Spaces.mixed 0 (i' + 1) R q.1 q.2
            = Real.sin (2 * q.2) * Work.Spaces.pth (Work.Spaces.mixed 0 i' R) q.1 q.2 from
          mixed_succ_th R i' q.1 q.2, hpth]
      exact mul_div_cancel₀ _ (hs0 q hq)
  · -- `j ≥ 1`: differentiate the lower jet in `z`
    obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    have hlow : ∀ r ∈ Work.FTS.EllipticEst.Q0,
        Work.Spaces.mixed j' i R r.1 r.2 = Φ j' i r.1 r.2 :=
      ih (j' + i) (by omega) j' i rfl (by omega)
    have hJet : TendstoLocallyUniformlyOn
        (fun n : ℕ => fderiv ℝ (Function.uncurry (Work.Spaces.mixed j' i (V n))))
        (fun p : ℝ × ℝ => Work.FTS.StrongEps.E5Aux.clmPair
          (Φ (j' + 1) i p.1 p.2 / p.1, Φ j' (i + 1) p.1 p.2 / Real.sin (2 * p.2)))
        Filter.atTop Work.FTS.EllipticEst.Q0 :=
      (Work.FTS.StrongEps.E5Aux.tendstoLocallyUniformlyOn_clmPair
        (hdivp1 j' i (by omega)) (hdivsn j' i (by omega))).congr
        (fun n => fun p hp => (fderiv_uncurry_mixed_eq_clmPair (hsm n) j' i hp).symm)
    have hderiv : HasFDerivAt (Function.uncurry (Work.Spaces.mixed j' i R))
        (Work.FTS.StrongEps.E5Aux.clmPair
          (Φ (j' + 1) i q.1 q.2 / q.1, Φ j' (i + 1) q.1 q.2 / Real.sin (2 * q.2))) q :=
      hasFDerivAt_of_slot_tlu (W := fun n => Work.Spaces.mixed j' i (V n))
        (F := Φ j' i) (R := Work.Spaces.mixed j' i R)
        hq (fun n p hp => hdiffV n j' i p hp) (hslot j' i (by omega)) hJet
        (fun p hp => hlow p hp)
    have hpz : Work.Spaces.pz (Work.Spaces.mixed j' i R) q.1 q.2
        = Φ (j' + 1) i q.1 q.2 / q.1 := by
      rw [Work.Spaces.pz_eq_fderiv hderiv.differentiableAt, hderiv.fderiv]
      simp
    rw [show Work.Spaces.mixed (j' + 1) i R q.1 q.2
          = q.1 * Work.Spaces.pz (Work.Spaces.mixed j' i R) q.1 q.2 from
        mixed_succ_left_eq R j' i q.1 q.2, hpz]
    exact mul_div_cancel₀ _ (hz0 q hq)

end Work.FTS.StrongEps.E5G
