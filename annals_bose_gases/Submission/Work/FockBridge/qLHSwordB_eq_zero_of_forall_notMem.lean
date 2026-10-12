import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FockBridge.Count
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The localised per-box potential word kills the `n_{B(u)} = 0` sector

`Work.SmallBoxSliding.qLHSwordB h M L d μ u Ψ` is the potential part of the localised
per-box energy word `E_{B(u)}(Ψ)` (FS `eq:BSsliding2`), i.e. the corpus word `qLHSword`
read at the `u`-localised kernels `wSmallPair M L d u v` and `wSmall1Pair h M L d u`:

    qLHSwordB … = ∫_{x ∈ abox N L} Ψ(x)² · ( − μ Σᵢ ∫_{y∈acube L} w_{1,B(u)}(xᵢ,y)
                                              + ½ Σ_{p ∈ pairSet N} w_{B(u)}(x_{p.1},x_{p.2}) ) .

Both localised kernels carry the two-factor cutoff `χ_{B(u)}(x) = χ(x/L)·χ_M(x/(Ld) − u)`
(`Submission.Work.ChiSmall.chiSmallB`) as a factor in **each** position.  By the support
containment of that cutoff (`chiSmallB_support_big_box`, `chiSmallB_support_small_box_dist`),
`χ_{B(u)}(z) ≠ 0` forces `z ∈ B(u) = dlBox L d u`.  Hence:

* if some coordinate `xᵢ` of the configuration lies in `B(u)`, the state hypothesis
  `Ψ x = 0` kills the integrand;
* if no coordinate lies in `B(u)`, then — since `x ∈ abox N L` puts every `xᵢ` in `acube L`
  — every cutoff factor `χ_{B(u)}(xᵢ)` vanishes, so *both* kernels vanish identically and the
  integrand is again `0`.

Either way the integrand vanishes pointwise on `abox N L`, and the word is `0`.
This is the `k = 0` sector of the Fock decomposition: the per-box word of an occupancy-`0`
sector piece is identically zero (the potential half of the `PerSectorBound` observation that
FS's `n = 0` sector contributes nothing).
-/

namespace Work.FockBridge

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open MeasureTheory
open scoped BigOperators

open Submission.BoseGases

/-! ## The support of the two-factor cutoff -/

/-- At `M = 0` the cosine-`M` bump degenerates: `χ_0 = (ζζζ)^0/√∫(ζζζ)^0 = 1/√∫1 = 0`. -/
lemma chiSmall_eq_zero_of_M_eq_zero (M : ℕ) (hM : M = 0) (z : ℝ³) :
    Submission.BoseGases.chiSmall M z = 0 := by
  subst hM
  have h : Submission.BoseGases.chiSmallNormSq 0 = 0 := by
    have hbase : ∀ z : ℝ³, Submission.BoseGases.chiSmallBase 0 z = 1 := fun z => by
      simp [Submission.BoseGases.chiSmallBase]
    dsimp only [Submission.BoseGases.chiSmallNormSq]
    simp only [hbase, one_pow, MeasureTheory.integral_const]
    rw [MeasureTheory.Measure.real, show (volume : Measure ℝ³) Set.univ = ⊤ by simp]
    simp
  simp [Submission.BoseGases.chiSmall, h]

/-- **The cutoff is supported in the small box**: for a point of the big box `acube L` that is
*not* in `B(u) = dlBox L d u`, the two-factor cutoff vanishes.  (For `M ≥ 1` this is the
contrapositive of `chiSmallB_support_big_box` + `chiSmallB_support_small_box_dist`; for `M = 0`
the bump is identically zero.) -/
lemma chiSmallB_eq_zero_of_mem_acube_of_notMem_dlBox (M : ℕ) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u z : ℝ³) (hz : z ∈ acube ℓ) (hz' : z ∉ dlBox ℓ d u) :
    Submission.BoseGases.chiSmallB M ℓ d u z = 0 := by
  rcases Nat.eq_zero_or_pos M with hM0 | hMpos
  · rw [Submission.BoseGases.chiSmallB, chiSmall_eq_zero_of_M_eq_zero M hM0]
    ring
  · have hM : 1 ≤ M := hMpos
    by_contra hx
    exact hz' (by
      rw [Submission.BoseGases.mem_dlBox_iff]
      refine ⟨hz, fun j => ?_⟩
      have h := Submission.BoseGases.chiSmallB_support_small_box_dist (M := M) hM hℓ hd hx j
      rw [abs_le] at h
      exact ⟨by linarith [h.1], by linarith [h.2]⟩)

/-! ## Vanishing of the localised kernels off the small box -/

/-- The localised two-body kernel `w_{B(u)}(z,y) = χ_{B(u)}(z)·W(z−y)·χ_{B(u)}(y)` vanishes
as soon as its **left** argument `z` is a big-box point outside the small box `B(u)`. -/
lemma wSmallPair_eq_zero_of_mem_acube_of_notMem_dlBox (M : ℕ) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : ℝ³) (hker : ℝ³ → ℝ) {z y : ℝ³} (hz : z ∈ acube ℓ) (hz' : z ∉ dlBox ℓ d u) :
    Submission.BoseGases.wSmallPair M ℓ d u hker z y = 0 := by
  rw [Submission.BoseGases.wSmallPair,
    chiSmallB_eq_zero_of_mem_acube_of_notMem_dlBox M hℓ hd u z hz hz']
  ring

/-- The one-body fibre of the localised one-body kernel vanishes at every big-box point
outside the small box: `∫_{y ∈ acube L} w_{1,B(u)}(z,y) dy = 0` for `z ∈ acube L ∖ B(u)`. -/
lemma wSmall1Pair_fibre_eq_zero_of_mem_acube_of_notMem_dlBox {v : ℝ³ → ℝ}
    (h : Work.UBB.ScatSol v) (M : ℕ) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : ℝ³) {z : ℝ³} (hz : z ∈ acube ℓ) (hz' : z ∉ dlBox ℓ d u) :
    (∫ y in acube ℓ, Submission.BoseGases.wSmall1Pair h M ℓ d u z y) = 0 := by
  have hpt : ∀ y : ℝ³, Submission.BoseGases.wSmall1Pair h M ℓ d u z y = 0 := fun y =>
    wSmallPair_eq_zero_of_mem_acube_of_notMem_dlBox M hℓ hd u (Submission.BoseGases.g0 v h) hz hz'
  rw [show (fun y : ℝ³ => Submission.BoseGases.wSmall1Pair h M ℓ d u z y) = fun _ => (0:ℝ) from
    funext hpt]
  simp

/-! ## The word vanishes on the `n_{B(u)} = 0` sector -/

/-- **The `k = 0` sector of the localised potential word.**  If the state `Ψ` vanishes on every
configuration with a particle in the small box `B(u) = dlBox L d u`, then the localised per-box
potential word `qLHSwordB` at that box vanishes: the integrand is pointwise zero on `abox N L`
(state hypothesis on the sector with a particle in `B(u)`, support of the cutoff factors on its
complement). -/
theorem qLHSwordB_eq_zero_of_forall_notMem {N : ℕ} {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : Work.UBB.ScatSol v) {M : ℕ} {L d μ : ℝ} (hL : 0 < L) (hd : 0 < d)
    {u : EuclideanSpace ℝ (Fin 3)}
    {Ψ : (Fin N → EuclideanSpace ℝ (Fin 3)) → ℝ}
    (hΨ : ∀ x : Fin N → EuclideanSpace ℝ (Fin 3),
      (∃ i : Fin N, x i ∈ Submission.BoseGases.dlBox L d u) → Ψ x = 0) :
    Work.SmallBoxSliding.qLHSwordB h M L d μ u Ψ = 0 := by
  classical
  rw [Work.SmallBoxSliding.qLHSwordB_eq_integral (v := v)]
  have hzero : ∀ x ∈ abox N L,
      Work.SmallBoxSliding.qLHSBIntegrand h M L d μ Ψ u x = 0 := by
    intro x hx
    rw [Submission.BoseGases.mem_abox_iff] at hx
    by_cases hc : ∃ i : Fin N, x i ∈ dlBox L d u
    · rw [Work.SmallBoxSliding.qLHSBIntegrand, hΨ x hc]
      ring
    · simp only [not_exists] at hc
      have h1 : (∑ i : Fin N, ∫ y in acube L,
          Submission.BoseGases.wSmall1Pair h M L d u (x i) y) = 0 :=
        Finset.sum_eq_zero (fun i _ =>
          wSmall1Pair_fibre_eq_zero_of_mem_acube_of_notMem_dlBox h M hL hd u (hx i) (hc i))
      have h2 : (∑ q ∈ pairSet N, Submission.BoseGases.wSmallPair M L d u v (x q.1) (x q.2)) = 0 :=
        Finset.sum_eq_zero (fun q _ =>
          wSmallPair_eq_zero_of_mem_acube_of_notMem_dlBox M hL hd u v (hx q.1) (hc q.1))
      rw [Work.SmallBoxSliding.qLHSBIntegrand, h1, h2]
      ring
  rw [show (∫ x in abox N L, Work.SmallBoxSliding.qLHSBIntegrand h M L d μ Ψ u x)
        = ∫ x in abox N L, (0 : ℝ) from
      MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_isClosed N L).measurableSet hzero]
  simp

end Work.FockBridge
