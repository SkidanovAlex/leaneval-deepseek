import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.FreqArc
import Submission.Work.BourgainPlan.IonescuWainger.tsum_prod_mul_conj_eq_integral_circConvFin
import Submission.Work.BourgainPlan.IonescuWainger.summable_prod_norm
import Submission.Work.BourgainPlan.IonescuWainger.continuous_circConvFin
import Submission.Work.BourgainPlan.IonescuWainger.norm_circConvFin_le
import Submission.Work.BourgainPlan.IonescuWainger.discFourier_mul_eq_circConv_l1
import Submission.Work.BourgainPlan.IonescuWainger.tsum_mul_conj_eq_integral_discFourier_l1

/-!
# The band-limited (`ℓ²`) extension of Tao's `ortho`(ii)/(iii)

Source: T. Tao, *The Ionescu–Wainger multiplier theorem and the adeles*, arXiv:2008.05066, §4
(Lemma `ortho`(ii)(iii)) — see `ARC_ARITH_STATUS.md` and `PLAN.md` for the lane.

The results of `FreqArc.lean` / `OrthoAssembly.lean` are stated for **finitely supported**
`ℤ`-functions.  The major-arc systems of the Ionescu–Wainger theorem are instead *band-limited*:
`f_α ∈ ℓ²(ℤ^d;H)` with Fourier support in a small arc around `α`.  This file performs the first
step of the extension, from finitely supported to **absolutely summable** data:

* `norm_fourier_apply`, `summable_discFourier`, `norm_discFourier_le` — for `h ∈ ℓ¹(ℤ)` the discrete
  Fourier transform `discFourier h : 𝕋 → ℂ` is an absolutely and uniformly convergent series, hence
  a bounded (indeed continuous) function with `‖𝓕h‖_∞ ≤ ‖h‖_{ℓ¹}`;
* `tendsto_Icc_neg_atTop` — the truncations `Finset.Icc (-N) N` are cofinal in the `atTop` filter of
  `Finset ℤ`;
* `discFourier_indicator_eq_sum`, `tendsto_discFourier_trunc` — the transforms of the truncations
  converge pointwise (uniformly) to the transform;
* `summable_mul_of_summable_norm`, `summable_prod_norm` — a finite pointwise product of absolutely
  summable sequences is absolutely summable (the domination used for the left-hand side);
* **`tsum_prod_mul_conj_eq_integral_circConvFin_l1`** — the pairing identity
  `Σ_m ∏_i f_i(m)·conj(∏_i g_i(m)) = ∫_𝕋 (✻_i 𝓕f_i)·conj(✻_i 𝓕g_i)`  for *absolutely summable*
  `f_i, g_i`, obtained from the finitely supported identity
  (`tsum_prod_mul_conj_eq_integral_circConvFin`) by dominated convergence along the truncations.

Together with the vanishing criterion `integral_circConvFin_mul_conj_eq_zero` of `FreqArc.lean` this
gives Tao's `ortho`(ii)/(iii) for absolutely summable major-arc systems, i.e.

`Σ_m ∏_i f_i(m)·conj(∏_i g_i(m)) = 0`

whenever the frequency supports lie in arcs whose Minkowski sums are disjoint.  The passage to *all*
band-limited `ℓ²` data is the next step of this lane (density of the smooth band-limited data plus
the `ℓ²`-continuity of both sides), and needs no new algebra.
-/

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.BourgainPlan.IonescuWainger

variable {n : ℕ}

/-! ## The discrete Fourier transform of an absolutely summable sequence -/

/-- `‖e^{2πi m ξ}‖ = 1`. -/
theorem norm_fourier_apply (m : ℤ) (ξ : Circle) : ‖fourier m ξ‖ = 1 := by
  rw [fourier_apply]
  exact Circle.norm_coe _

/-- The series defining `discFourier h ξ` is absolutely summable when `h ∈ ℓ¹(ℤ)`. -/
theorem summable_discFourier {h : ℤ → ℂ} (hh : Summable fun m => ‖h m‖) (ξ : Circle) :
    Summable fun m : ℤ => h m * fourier m ξ := by
  refine Summable.of_norm_bounded hh fun m => ?_
  have h1 : ‖fourier m ξ‖ = 1 := norm_fourier_apply m ξ
  rw [norm_mul, h1, mul_one]

/-- **The transform of an `ℓ¹` sequence is bounded by its `ℓ¹` norm.** -/
theorem norm_discFourier_le {h : ℤ → ℂ} (hh : Summable fun m => ‖h m‖) (ξ : Circle) :
    ‖discFourier h ξ‖ ≤ ∑' m : ℤ, ‖h m‖ := by
  have hs : Summable (fun m : ℤ => h m * fourier m ξ) := summable_discFourier hh ξ
  have h1 : ‖∑' m : ℤ, h m * fourier m ξ‖ ≤ ∑' m : ℤ, ‖h m * fourier m ξ‖ :=
    norm_tsum_le_tsum_norm hs.norm
  have h2 : (∑' m : ℤ, ‖h m * fourier m ξ‖) = ∑' m : ℤ, ‖h m‖ :=
    tsum_congr fun m => by rw [norm_mul, norm_fourier_apply, mul_one]
  rw [h2] at h1
  simpa only [discFourier] using h1

/-- The transform of the truncation of `h` to a finite set `s` is the corresponding finite sum. -/
theorem discFourier_indicator_eq_sum (h : ℤ → ℂ) (s : Finset ℤ) (ξ : Circle) :
    discFourier (fun m => if m ∈ s then h m else 0) ξ = ∑ m ∈ s, h m * fourier m ξ := by
  rw [discFourier_eq_sum_of_support (s := s) (fun m hm => by simp [hm]) ξ]
  exact Finset.sum_congr rfl fun m hm => by rw [if_pos hm]

/-- The truncations `Finset.Icc (-N) N` are cofinal in the `atTop` filter of `Finset ℤ`. -/
theorem tendsto_Icc_neg_atTop :
    Filter.Tendsto (fun N : ℕ => Finset.Icc (-(N : ℤ)) (N : ℤ)) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop]
  intro b
  rw [Filter.eventually_atTop]
  refine ⟨b.sup (fun m => m.natAbs) + 1, fun N hN m hm => ?_⟩
  rw [Finset.mem_Icc]
  have h1 : m.natAbs ≤ b.sup (fun m : ℤ => m.natAbs) :=
    Finset.le_sup (f := fun m : ℤ => m.natAbs) hm
  have h2 : m.natAbs ≤ N := by omega
  have h3 : ((m.natAbs : ℕ) : ℤ) ≤ (N : ℤ) := by exact_mod_cast h2
  constructor
  · have h4 : -(m.natAbs : ℤ) ≤ m := by
      rw [Int.natCast_natAbs]
      exact neg_abs_le m
    omega
  · have h4 : m ≤ (m.natAbs : ℤ) := Int.le_natAbs
    omega

/-- The transforms of the truncations converge to the transform of `h` (pointwise, uniformly). -/
theorem tendsto_discFourier_trunc {h : ℤ → ℂ} (hh : Summable fun m => ‖h m‖) (ξ : Circle) :
    Filter.Tendsto
      (fun N : ℕ => ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), h m * fourier m ξ)
      Filter.atTop (nhds (discFourier h ξ)) :=
  (summable_discFourier hh ξ).hasSum.comp tendsto_Icc_neg_atTop

/-! ## The pointwise product of absolutely summable sequences -/

/-- The pointwise product of absolutely summable sequences is absolutely summable. -/
theorem summable_norm_prod {n : ℕ} (f : Fin (n + 1) → ℤ → ℂ)
    (hf : ∀ i, Summable fun m => ‖f i m‖) :
    Summable fun m => ∏ i, ‖f i m‖ :=
  summable_prod_norm (fun i => fun m => ‖f i m‖) (fun i => hf i) fun i m => norm_nonneg _

/-- The pointwise product of absolutely summable functions is absolutely summable. -/
theorem summable_prod_fin {n : ℕ} (f : Fin (n + 1) → ℤ → ℂ)
    (hf : ∀ i, Summable fun m => ‖f i m‖) :
    Summable fun m => ∏ i, f i m := by
  have h := summable_norm_prod f hf
  refine Summable.of_norm_bounded h fun m => ?_
  rw [norm_prod]

/-! ## The `ℓ¹` extension of the Fourier identities -/

/-- **The Fourier transform of a finite product is the iterated convolution of the transforms**,
for *absolutely summable* factors. -/
theorem discFourier_finprod_eq_circConvFin_l1 {n : ℕ} (f : Fin (n + 1) → ℤ → ℂ)
    (hf : ∀ i, Summable fun m => ‖f i m‖) :
    discFourier (fun m => ∏ i, f i m) = circConvFin (n + 1) (fun i => discFourier (f i)) := by
  induction n with
  | zero =>
      have h1 : (fun m : ℤ => ∏ i : Fin 1, f i m) = f 0 := by
        funext m; exact Fin.prod_univ_one fun i : Fin 1 => f i m
      rw [h1]
      rfl
  | succ n ih =>
      have hrec : discFourier (fun m => ∏ i : Fin (n + 1), f i.castSucc m)
          = circConvFin (n + 1) (fun i => discFourier (f i.castSucc)) :=
        ih (fun i => f i.castSucc) (fun i => hf i.castSucc)
      have hsplit : (fun m : ℤ => ∏ i : Fin (n + 1 + 1), f i m)
          = fun m : ℤ =>
              (∏ i : Fin (n + 1), f i.castSucc m) * f (Fin.last (n + 1)) m :=
        funext fun m => Fin.prod_univ_castSucc fun i : Fin (n + 1 + 1) => f i m
      funext ξ
      calc discFourier (fun m => ∏ i, f i m) ξ
          = discFourier (fun m => (∏ i : Fin (n + 1), f i.castSucc m)
              * f (Fin.last (n + 1)) m) ξ := by rw [hsplit]
        _ = circConv (discFourier (fun m => ∏ i : Fin (n + 1), f i.castSucc m))
              (discFourier (f (Fin.last (n + 1)))) ξ :=
              discFourier_mul_eq_circConv_l1
                (summable_prod_fin (fun i : Fin (n + 1) => f i.castSucc)
                  (fun i => hf i.castSucc)).norm (hf (Fin.last (n + 1))) ξ
        _ = circConv (circConvFin (n + 1) (fun i => discFourier (f i.castSucc)))
              (discFourier (f (Fin.last (n + 1)))) ξ := by rw [hrec]
        _ = circConvFin (n + 1 + 1) (fun i => discFourier (f i)) ξ := rfl

/-- **Tao's `ortho`(ii)/(iii), Fourier side, for absolutely summable data.**  For absolutely
summable `f i, g i : ℤ → ℂ`,

`Σ_m (∏_i f i m)·conj (∏_i g i m) = ∫_𝕋 (✻_i 𝓕(f i))(ξ)·conj ((✻_i 𝓕(g i))(ξ)) dξ`. -/
theorem tsum_prod_mul_conj_eq_integral_circConvFin_l1 {n : ℕ} (f g : Fin (n + 1) → ℤ → ℂ)
    (hf : ∀ i, Summable fun m => ‖f i m‖) (hg : ∀ i, Summable fun m => ‖g i m‖) :
    ∑' m : ℤ, (∏ i, f i m) * star (∏ i, g i m)
      = ∫ ξ : Circle, circConvFin (n + 1) (fun i => discFourier (f i)) ξ
          * star (circConvFin (n + 1) (fun i => discFourier (g i)) ξ)
          ∂AddCircle.haarAddCircle := by
  have hF : Summable fun m : ℤ => ‖∏ i, f i m‖ := (summable_prod_fin f hf).norm
  have hG : Summable fun m : ℤ => ‖∏ i, g i m‖ := (summable_prod_fin g hg).norm
  have h1 := discFourier_finprod_eq_circConvFin_l1 f hf
  have h2 := discFourier_finprod_eq_circConvFin_l1 g hg
  rw [tsum_mul_conj_eq_integral_discFourier_l1 hF hG]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  show discFourier (fun m => ∏ i, f i m) ξ * star (discFourier (fun m => ∏ i, g i m) ξ)
      = circConvFin (n + 1) (fun i => discFourier (f i)) ξ
        * star (circConvFin (n + 1) (fun i => discFourier (g i)) ξ)
  rw [h1, h2]

/-! ## Tao's `ortho`(ii)/(iii) for absolutely summable major-arc systems -/

/-- **Tao's `ortho`(ii) (denominator orthogonality) for absolutely summable data.**  The
`ℓ¹`-analogue of `tsum_prod_mul_conj_eq_zero_of_nonce`: the same conclusion for functions which are
merely absolutely summable, with the frequency supports (of the *continuous* transforms
`discFourier`, which exist for `ℓ¹` data) in the arcs.  This is the class of band-limited systems
with an absolutely convergent Fourier series. -/
theorem tsum_prod_mul_conj_eq_zero_of_nonce_l1 {n : ℕ} {S : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    {A : Fin (n + 1) ⊕ Fin (n + 1) → Finset ℕ} (hA : ∀ j, A j ⊆ S) (hnonce : HasNonce A)
    {f : Fin (n + 1) ⊕ Fin (n + 1) → ℤ → ℂ} (hf : ∀ j, Summable fun m => ‖f j m‖)
    {α β : Fin (n + 1) → Circle} (hα : ∀ i, α i ∈ sigmaA (A (Sum.inl i)))
    (hβ : ∀ i, β i ∈ sigmaA (A (Sum.inr i))) {ε : ℝ}
    (hF : ∀ i, ∀ ξ, ξ ∉ arcSet (α i) ε → discFourier (f (Sum.inl i)) ξ = 0)
    (hG : ∀ i, ∀ ξ, ξ ∉ arcSet (β i) ε → discFourier (f (Sum.inr i)) ξ = 0)
    (hsmall : 2 * ((n + 1 : ℕ) : ℝ) * ε < 1 / ((∏ j, QA (A j) : ℕ) : ℝ)) :
    ∑' m : ℤ, (∏ i, f (Sum.inl i) m) * star (∏ i, f (Sum.inr i) m) = 0 := by
  rw [tsum_prod_mul_conj_eq_integral_circConvFin_l1 (fun i => f (Sum.inl i))
    (fun i => f (Sum.inr i)) (fun i => hf (Sum.inl i)) (fun i => hf (Sum.inr i))]
  exact integral_circConvFin_mul_conj_eq_zero hF hG
    (disjoint_setSumFin_arcSet_of_nonce h2 hS hA hnonce hα hβ hsmall)

/-- **Tao's `ortho`(iii) (numerator orthogonality) for absolutely summable data.**  The
`ℓ¹`-analogue of `tsum_prod_mul_conj_eq_zero_of_petal`. -/
theorem tsum_prod_mul_conj_eq_zero_of_petal_l1 {n : ℕ} {S : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    {P : Fin (n + 1) → Finset ℕ} (hP : ∀ i, P i ⊆ S)
    (hdisj : ∀ i j : Fin (n + 1), i ≠ j → Disjoint (P i) (P j))
    {f g : Fin (n + 1) → ℤ → ℂ} (hf : ∀ i, Summable fun m => ‖f i m‖)
    (hg : ∀ i, Summable fun m => ‖g i m‖)
    {α β : Fin (n + 1) → Circle} (hα : ∀ i, α i ∈ sigmaA (P i)) (hβ : ∀ i, β i ∈ sigmaA (P i))
    (hne : ∃ i, α i ≠ β i) {ε : ℝ}
    (hF : ∀ i, ∀ ξ, ξ ∉ arcSet (α i) ε → discFourier (f i) ξ = 0)
    (hG : ∀ i, ∀ ξ, ξ ∉ arcSet (β i) ε → discFourier (g i) ξ = 0)
    (hsmall : 2 * ((n + 1 : ℕ) : ℝ) * ε < 1 / ((∏ i, QA (P i) : ℕ) : ℝ)) :
    ∑' m : ℤ, (∏ i, f i m) * star (∏ i, g i m) = 0 := by
  rw [tsum_prod_mul_conj_eq_integral_circConvFin_l1 f g hf hg]
  exact integral_circConvFin_mul_conj_eq_zero hF hG
    (disjoint_setSumFin_arcSet_of_petal h2 hS hP hdisj hα hβ hne hsmall)

end Work.BourgainPlan.IonescuWainger
