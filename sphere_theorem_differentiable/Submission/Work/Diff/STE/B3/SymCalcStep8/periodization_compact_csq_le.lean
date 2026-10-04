import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.periodization_contDiff_periodic
import Submission.Work.Diff.STE.B3.CSq_period_le_integral_deriv
import Submission.Work.Diff.STE.CSq_periodization_le_of_sup_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `Hᵗ` norm of a periodisation is bounded by the physical derivatives

For a smooth function `Φ : (ι → ℝ) → ℂ` whose **topological** support is contained in a compact
set `K` — in particular `Φ` need not be supported in the unit cube — the periodisation

`P Φ = ∑' m : ι → ℤ, Φ (· + m)`

is smooth and `1`-periodic, and

`CSq t (fourierCoeff (P Φ)) ≤ C * Σ_{m ≤ t} Σ_{l : Fin m → ι} ∫ ‖∂^l Φ‖²`

with a constant `C` depending only on `t`, `ι` and `K`.

The only difference from `CSq_period_le_integral_deriv` (which requires `supp φ ⊆ (-1/2,1/2)^ι`)
is *locality of the periodisation*: since `K` is bounded, say `K ⊆ closedBall 0 R`, on the closed
unit cube only the lattice vectors `n` with `nᵢ ∈ [-M,M]`, `M = ⌈R+2⌉`, can contribute to the sum,
uniformly in the point of the cube.  So on the cube `P Φ` is a *finite* sum of translates of `Φ`
(with a set of indices independent of `Φ`), and the whole argument of
`CSq_period_le_integral_deriv` goes through with `card (latBox M)²` in place of
`card (csqp_boxIdx ι)²`.

## Main ingredients

* `periodization_eventuallyEq_latBox`: near a point `z` the periodisation agrees with the finite
  sum over the lattice box, with the size of the box controlled by `‖z‖`, `R` and the compactness
  of `K`.
* `contDiff_periodization_of_compact`: `P Φ` is smooth (from the local finite-sum description).
* `ENormSq_periodization_le_of_compact`: the `L²`-energy of `P Φ` on the cube is bounded by the
  physical `L²`-norms of the derivatives of `Φ` over all of `ℝ^ι` (converting
  `∫_{cube} ‖∂^l Φ (· + n)‖²` into `∫_ℝ ‖∂^l Φ‖²` by translation invariance).
* `CSq_le_ENormSq` (torus Sobolev comparison) and `periodization_periodic` finish the proof.
-/

noncomputable section

namespace Work.Diff.STE.B3.SymCalcStep8

open MeasureTheory Filter
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The box of lattice vectors all of whose coordinates lie in `[-M, M]`. -/
def latBox (ι : Type*) [Fintype ι] [DecidableEq ι] (M : ℤ) : Finset (ι → ℤ) :=
  Fintype.piFinset fun _ : ι => Finset.Icc (-M) M

lemma mem_latBox {M : ℤ} {n : ι → ℤ} :
    n ∈ latBox ι M ↔ ∀ i, n i ∈ Finset.Icc (-M) M := by
  rw [latBox, Fintype.mem_piFinset]

/-! ## Locality of the periodisation -/

/-- **Local finiteness of the periodisation.**  If `Φ` is supported in the compact set `K`,
contained in the closed ball of radius `R`, and `z` has all coordinates bounded by `a`, then in a
neighbourhood of `z` the periodisation of `Φ` agrees with the finite sum over the lattice box
`[-M, M]^ι` with `M = ⌈R + a + 1⌉`. -/
lemma periodization_eventuallyEq_latBox {Φ : (ι → ℝ) → ℂ} {K : Set (ι → ℝ)} {R a : ℝ}
    (hKb : K ⊆ Metric.closedBall 0 R) (hΦK : tsupport Φ ⊆ K) {z : ι → ℝ}
    (hz : ∀ i, |z i| ≤ a) :
    (fun y : ι → ℝ => ∑' n : ι → ℤ, Φ (y + Work.Diff.STE.iVec n))
      =ᶠ[nhds z] (fun y : ι → ℝ => ∑ n ∈ latBox ι ⌈R + a + 1⌉,
        Φ (y + Work.Diff.STE.iVec n)) := by
  refine Filter.eventually_of_mem (Metric.ball_mem_nhds z one_pos) fun y hy => ?_
  refine tsum_eq_sum (s := latBox ι ⌈R + a + 1⌉) fun n hn => ?_
  by_contra hne
  have hmem : y + Work.Diff.STE.iVec n ∈ tsupport Φ := subset_closure hne
  have hR : ‖y + Work.Diff.STE.iVec n‖ ≤ R := by
    have h := hKb (hΦK hmem)
    rwa [Metric.mem_closedBall, dist_zero_right] at h
  have hyz : ‖y - z‖ < 1 := by
    have h := hy
    rwa [Metric.mem_ball, dist_eq_norm] at h
  apply hn
  rw [mem_latBox]
  intro i
  rw [Finset.mem_Icc]
  have hycoord : |y i| ≤ a + 1 := by
    have h1 : |y i - z i| ≤ ‖y - z‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm (y - z) i
    have h3 : |y i| ≤ |y i - z i| + |z i| := by
      calc |y i| = |(y i - z i) + z i| := by rw [sub_add_cancel]
        _ ≤ |y i - z i| + |z i| := abs_add_le _ _
    have h2 : |z i| ≤ a := hz i
    linarith
  have hni : |(n i : ℝ)| ≤ R + a + 1 := by
    have hsplit : (n i : ℝ) = (y + Work.Diff.STE.iVec n) i - y i := by simp
    calc |(n i : ℝ)| = |(y + Work.Diff.STE.iVec n) i - y i| := by rw [hsplit]
      _ ≤ |(y + Work.Diff.STE.iVec n) i| + |y i| := abs_sub _ _
      _ ≤ ‖y + Work.Diff.STE.iVec n‖ + |y i| := by
          have h := norm_le_pi_norm (y + Work.Diff.STE.iVec n) i
          rw [Real.norm_eq_abs] at h
          linarith
      _ ≤ R + a + 1 := by linarith
  have hceil : ((⌈R + a + 1⌉ : ℤ) : ℝ) ≥ R + a + 1 := Int.le_ceil _
  have hcast : ((|n i| : ℤ) : ℝ) = |(n i : ℝ)| := Int.cast_abs
  have hle : ((|n i| : ℤ) : ℝ) ≤ ((⌈R + a + 1⌉ : ℤ) : ℝ) := by rw [hcast]; linarith
  have habs : |n i| ≤ ⌈R + a + 1⌉ := by exact_mod_cast hle
  exact abs_le.mp habs

/-- The periodisation of a smooth function with compact support is smooth, being locally a finite
sum of translates. -/
lemma contDiff_periodization_of_compact {Φ : (ι → ℝ) → ℂ} {K : Set (ι → ℝ)} {R : ℝ}
    (hKb : K ⊆ Metric.closedBall 0 R) (hΦK : tsupport Φ ⊆ K)
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : ι → ℝ => ∑' n : ι → ℤ, Φ (y + Work.Diff.STE.iVec n)) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  have hz : ∀ i : ι, |z i| ≤ ‖z‖ := by
    intro i
    simpa [Real.norm_eq_abs] using norm_le_pi_norm z i
  have hev := periodization_eventuallyEq_latBox (a := ‖z‖) hKb hΦK hz
  have hfin : ContDiff ℝ (⊤ : ℕ∞) (fun y : ι → ℝ =>
      ∑ n ∈ latBox ι ⌈R + ‖z‖ + 1⌉, Φ (y + Work.Diff.STE.iVec n)) := by
    apply ContDiff.sum
    intro n _
    have hshift : ContDiff ℝ (⊤ : ℕ∞) (fun y : ι → ℝ => y + Work.Diff.STE.iVec n) := by
      simpa using (contDiff_id.add (contDiff_const : ContDiff ℝ (⊤ : ℕ∞)
        (fun _ : ι → ℝ => Work.Diff.STE.iVec n)))
    exact hΦ.comp hshift
  exact hfin.contDiffAt.congr_of_eventuallyEq hev

/-- On the closed unit cube the iterated partial derivatives of the periodisation of `Φ` are the
finite sum of the corresponding derivatives of the translates `Φ (· + n)`, `n ∈ latBox ⌈R+2⌉`. -/
lemma pdVec_periodization_eq_sum_latBox {Φ : (ι → ℝ) → ℂ} {K : Set (ι → ℝ)} {R : ℝ}
    (hKb : K ⊆ Metric.closedBall 0 R) (hΦK : tsupport Φ ⊆ K)
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) {x : ι → ℝ} (hx : x ∈ Work.Diff.STE.unitCube)
    (m : ℕ) (l : Fin m → ι) :
    Work.Diff.STE.pdVec m l (fun y : ι → ℝ => ∑' n : ι → ℤ, Φ (y + Work.Diff.STE.iVec n)) x
      = ∑ n ∈ latBox ι ⌈R + 1 + 1⌉,
          Work.Diff.STE.pdVec m l Φ (x + Work.Diff.STE.iVec n) := by
  have hx1 : ∀ i : ι, |x i| ≤ 1 := by
    intro i
    have h := Set.mem_pi.mp hx i (Set.mem_univ i)
    rw [Set.mem_Ioc] at h
    rw [abs_of_pos h.1]
    exact h.2
  have hev := periodization_eventuallyEq_latBox (a := 1) hKb hΦK hx1
  rw [Work.Diff.STE.csqp_pdVec_congr l hev]
  rw [Work.Diff.STE.csqp_pdVec_finset_sum l (latBox ι ⌈R + 1 + 1⌉)
      (fun n y => Φ (y + Work.Diff.STE.iVec n)) x]
  · exact Finset.sum_congr rfl fun n _ => Work.Diff.STE.csqp_pdVec_comp_add_right l Φ _ x
  · intro n _
    have hshift : ContDiff ℝ (⊤ : ℕ∞) (fun y : ι → ℝ => y + Work.Diff.STE.iVec n) := by
      simpa using (contDiff_id.add (contDiff_const : ContDiff ℝ (⊤ : ℕ∞)
        (fun _ : ι → ℝ => Work.Diff.STE.iVec n)))
    exact hΦ.comp hshift

/-! ## The energy estimate -/

/-- The `L²`-norm squared of an iterated derivative of a smooth compactly supported function is
integrable on `ℝ^ι`. -/
lemma integrable_normSq_pdVec_of_compact {Φ : (ι → ℝ) → ℂ} {K : Set (ι → ℝ)}
    (hK : IsCompact K) (hΦK : tsupport Φ ⊆ K) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (m : ℕ) (l : Fin m → ι) :
    Integrable (fun x : ι → ℝ => ‖Work.Diff.STE.pdVec m l Φ x‖ ^ 2) volume := by
  have hcont : Continuous (fun x : ι → ℝ => ‖Work.Diff.STE.pdVec m l Φ x‖ ^ 2) :=
    ((Work.Diff.STE.csqp_contDiff_pdList_top (List.ofFn l) hΦ).continuous.norm.pow 2)
  refine hcont.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.of_support_subset_isCompact hK ?_
  intro x hx
  have hne : Work.Diff.STE.pdVec m l Φ x ≠ 0 := by
    intro h0
    exact hx (by simp [h0])
  exact hΦK (Work.Diff.STE.csqp_support_pdList_subset_closure (List.ofFn l) Φ hne)

/-- **The energy of the periodisation is controlled by the physical derivatives.**  For a smooth
`Φ` supported in a compact set contained in the closed ball of radius `R`,

`ENormSq m (P Φ) ≤ (card (latBox ⌈R+2⌉))² * Σ_{l : Fin m → ι} ∫_ℝ ‖∂^l Φ‖²`. -/
lemma ENormSq_periodization_le_of_compact {Φ : (ι → ℝ) → ℂ} {K : Set (ι → ℝ)} {R : ℝ}
    (hK : IsCompact K) (hKb : K ⊆ Metric.closedBall 0 R) (hΦK : tsupport Φ ⊆ K)
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (m : ℕ) :
    Work.Diff.STE.ENormSq m (fun y : ι → ℝ => ∑' n : ι → ℤ, Φ (y + Work.Diff.STE.iVec n))
      ≤ ((latBox ι ⌈R + 1 + 1⌉).card : ℝ) ^ 2
          * ∑ l : Fin m → ι, ∫ x : ι → ℝ, ‖Work.Diff.STE.pdVec m l Φ x‖ ^ 2 := by
  have hPcd := contDiff_periodization_of_compact hKb hΦK hΦ
  have hIntPhi : ∀ l : Fin m → ι,
      Integrable (fun x : ι → ℝ => ‖Work.Diff.STE.pdVec m l Φ x‖ ^ 2) volume :=
    fun l => integrable_normSq_pdVec_of_compact hK hΦK hΦ m l
  have hterm : ∀ l : Fin m → ι,
      ∫ x in Work.Diff.STE.unitCube,
          ‖Work.Diff.STE.pdVec m l
            (fun y : ι → ℝ => ∑' n : ι → ℤ, Φ (y + Work.Diff.STE.iVec n)) x‖ ^ 2
        ≤ ((latBox ι ⌈R + 1 + 1⌉).card : ℝ) ^ 2
            * ∫ x : ι → ℝ, ‖Work.Diff.STE.pdVec m l Φ x‖ ^ 2 := by
    intro l
    have hcontpd : Continuous (fun x : ι → ℝ => Work.Diff.STE.pdVec m l Φ x) :=
      (Work.Diff.STE.csqp_contDiff_pdList_top (List.ofFn l) hΦ).continuous
    have hpt : ∀ x ∈ Work.Diff.STE.unitCube,
        ‖Work.Diff.STE.pdVec m l
          (fun y : ι → ℝ => ∑' n : ι → ℤ, Φ (y + Work.Diff.STE.iVec n)) x‖ ^ 2
          ≤ ((latBox ι ⌈R + 1 + 1⌉).card : ℝ)
              * ∑ n ∈ latBox ι ⌈R + 1 + 1⌉,
                  ‖Work.Diff.STE.pdVec m l Φ (x + Work.Diff.STE.iVec n)‖ ^ 2 := by
      intro x hx
      rw [pdVec_periodization_eq_sum_latBox hKb hΦK hΦ hx m l]
      calc ‖∑ n ∈ latBox ι ⌈R + 1 + 1⌉,
              Work.Diff.STE.pdVec m l Φ (x + Work.Diff.STE.iVec n)‖ ^ 2
          ≤ (∑ n ∈ latBox ι ⌈R + 1 + 1⌉,
              ‖Work.Diff.STE.pdVec m l Φ (x + Work.Diff.STE.iVec n)‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
        _ ≤ ((latBox ι ⌈R + 1 + 1⌉).card : ℝ)
              * ∑ n ∈ latBox ι ⌈R + 1 + 1⌉,
                  ‖Work.Diff.STE.pdVec m l Φ (x + Work.Diff.STE.iVec n)‖ ^ 2 :=
            sq_sum_le_card_mul_sum_sq
    have hcontR : Continuous (fun x : ι → ℝ =>
        ((latBox ι ⌈R + 1 + 1⌉).card : ℝ)
          * ∑ n ∈ latBox ι ⌈R + 1 + 1⌉,
              ‖Work.Diff.STE.pdVec m l Φ (x + Work.Diff.STE.iVec n)‖ ^ 2) :=
      continuous_const.mul (continuous_finsetSum _ (fun n _ =>
        ((hcontpd.comp (continuous_id.add continuous_const)).norm.pow 2)))
    have hInt1 : IntegrableOn
        (fun x : ι → ℝ => ‖Work.Diff.STE.pdVec m l
          (fun y : ι → ℝ => ∑' n : ι → ℤ, Φ (y + Work.Diff.STE.iVec n)) x‖ ^ 2)
        (Work.Diff.STE.unitCube) volume :=
      Work.Diff.STE.csqp_integrableOn_unitCube_of_continuous_real
        (((Work.Diff.STE.csqp_contDiff_pdList_top (List.ofFn l) hPcd).continuous).norm.pow 2)
    have hInt2 : IntegrableOn (fun x : ι → ℝ =>
        ((latBox ι ⌈R + 1 + 1⌉).card : ℝ)
          * ∑ n ∈ latBox ι ⌈R + 1 + 1⌉,
              ‖Work.Diff.STE.pdVec m l Φ (x + Work.Diff.STE.iVec n)‖ ^ 2)
        (Work.Diff.STE.unitCube) volume :=
      Work.Diff.STE.csqp_integrableOn_unitCube_of_continuous_real hcontR
    have hmono := setIntegral_mono_on hInt1 hInt2
      (Work.Diff.STE.BesselCont.measSet_unitCube (ι := ι)) hpt
    have hsplit : ∫ x in Work.Diff.STE.unitCube,
          ((latBox ι ⌈R + 1 + 1⌉).card : ℝ)
            * ∑ n ∈ latBox ι ⌈R + 1 + 1⌉,
                ‖Work.Diff.STE.pdVec m l Φ (x + Work.Diff.STE.iVec n)‖ ^ 2
        = ((latBox ι ⌈R + 1 + 1⌉).card : ℝ) * ∑ n ∈ latBox ι ⌈R + 1 + 1⌉,
            ∫ x in Work.Diff.STE.unitCube,
              ‖Work.Diff.STE.pdVec m l Φ (x + Work.Diff.STE.iVec n)‖ ^ 2 := by
      rw [integral_const_mul]
      congr 1
      rw [integral_finsetSum]
      intro n _
      exact ((hIntPhi l).comp_add_right (Work.Diff.STE.iVec n)).integrableOn
    have htr : ∀ n ∈ latBox ι ⌈R + 1 + 1⌉,
        ∫ x in Work.Diff.STE.unitCube,
            ‖Work.Diff.STE.pdVec m l Φ (x + Work.Diff.STE.iVec n)‖ ^ 2
          ≤ ∫ x : ι → ℝ, ‖Work.Diff.STE.pdVec m l Φ x‖ ^ 2 := by
      intro n _
      rw [Work.Diff.STE.B3.steB3_setIntegral_comp_add_real (Work.Diff.STE.iVec n)
        (Work.Diff.STE.unitCube) (fun z : ι → ℝ => ‖Work.Diff.STE.pdVec m l Φ z‖ ^ 2)]
      exact setIntegral_le_integral (hIntPhi l)
        (Filter.Eventually.of_forall fun x => by positivity)
    calc ∫ x in Work.Diff.STE.unitCube,
            ‖Work.Diff.STE.pdVec m l
              (fun y : ι → ℝ => ∑' n : ι → ℤ, Φ (y + Work.Diff.STE.iVec n)) x‖ ^ 2
        ≤ ∫ x in Work.Diff.STE.unitCube,
            ((latBox ι ⌈R + 1 + 1⌉).card : ℝ)
              * ∑ n ∈ latBox ι ⌈R + 1 + 1⌉,
                  ‖Work.Diff.STE.pdVec m l Φ (x + Work.Diff.STE.iVec n)‖ ^ 2 := hmono
      _ = ((latBox ι ⌈R + 1 + 1⌉).card : ℝ) * ∑ n ∈ latBox ι ⌈R + 1 + 1⌉,
            ∫ x in Work.Diff.STE.unitCube,
              ‖Work.Diff.STE.pdVec m l Φ (x + Work.Diff.STE.iVec n)‖ ^ 2 := hsplit
      _ ≤ ((latBox ι ⌈R + 1 + 1⌉).card : ℝ) * ∑ n ∈ latBox ι ⌈R + 1 + 1⌉,
            ∫ x : ι → ℝ, ‖Work.Diff.STE.pdVec m l Φ x‖ ^ 2 :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum htr) (by positivity)
      _ = ((latBox ι ⌈R + 1 + 1⌉).card : ℝ)
            * (((latBox ι ⌈R + 1 + 1⌉).card : ℝ)
                * ∫ x : ι → ℝ, ‖Work.Diff.STE.pdVec m l Φ x‖ ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = ((latBox ι ⌈R + 1 + 1⌉).card : ℝ) ^ 2
            * ∫ x : ι → ℝ, ‖Work.Diff.STE.pdVec m l Φ x‖ ^ 2 := by ring
  calc Work.Diff.STE.ENormSq m (fun y : ι → ℝ => ∑' n : ι → ℤ, Φ (y + Work.Diff.STE.iVec n))
      = ∑ l : Fin m → ι, ∫ x in Work.Diff.STE.unitCube,
          ‖Work.Diff.STE.pdVec m l
            (fun y : ι → ℝ => ∑' n : ι → ℤ, Φ (y + Work.Diff.STE.iVec n)) x‖ ^ 2 := rfl
    _ ≤ ∑ l : Fin m → ι, ((latBox ι ⌈R + 1 + 1⌉).card : ℝ) ^ 2
          * ∫ x : ι → ℝ, ‖Work.Diff.STE.pdVec m l Φ x‖ ^ 2 :=
        Finset.sum_le_sum fun l _ => hterm l
    _ = ((latBox ι ⌈R + 1 + 1⌉).card : ℝ) ^ 2
          * ∑ l : Fin m → ι, ∫ x : ι → ℝ, ‖Work.Diff.STE.pdVec m l Φ x‖ ^ 2 := by
        rw [Finset.mul_sum]

/-! ## The target theorem -/

theorem periodization_compact_csq_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ℕ) (K : Set (ι → ℝ)) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Φ : (ι → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ → tsupport Φ ⊆ K →
      Work.Diff.STE.CSq t (Work.Diff.STE.fourierCoeff
          (fun z : ι → ℝ => ∑' m : ι → ℤ, Φ (z + Work.Diff.STE.iVec m)))
        ≤ C * ∑ m ∈ Finset.range (t + 1), ∑ l : Fin m → ι,
            ∫ x : ι → ℝ, ‖Work.Diff.STE.pdVec m l Φ x‖ ^ 2 := by
  classical
  obtain ⟨C₀, hC₀nn, hC₀⟩ := Work.Diff.STE.CSq_le_ENormSq (ι := ι) t
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ι → ℝ)
  refine ⟨C₀ * 2 * ((latBox ι ⌈R + 1 + 1⌉).card : ℝ) ^ 2, by positivity, ?_⟩
  intro Φ hΦ hΦK
  set T : ℝ := ∑ m ∈ Finset.range (t + 1), ∑ l : Fin m → ι,
      ∫ x : ι → ℝ, ‖Work.Diff.STE.pdVec m l Φ x‖ ^ 2 with hT
  have htermnn : ∀ m ∈ Finset.range (t + 1),
      0 ≤ ∑ l : Fin m → ι, ∫ x : ι → ℝ, ‖Work.Diff.STE.pdVec m l Φ x‖ ^ 2 :=
    fun m _ => Finset.sum_nonneg fun l _ => integral_nonneg fun x => by positivity
  have htT : ∑ l : Fin t → ι, ∫ x : ι → ℝ, ‖Work.Diff.STE.pdVec t l Φ x‖ ^ 2 ≤ T := by
    rw [hT]
    exact Finset.single_le_sum htermnn (Finset.mem_range.mpr (by omega))
  have h0T : ∑ l : Fin 0 → ι, ∫ x : ι → ℝ, ‖Work.Diff.STE.pdVec 0 l Φ x‖ ^ 2 ≤ T := by
    rw [hT]
    exact Finset.single_le_sum htermnn (Finset.mem_range.mpr (by omega))
  have hPcd : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : ι → ℝ => ∑' m : ι → ℤ, Φ (z + Work.Diff.STE.iVec m)) :=
    contDiff_periodization_of_compact hR hΦK hΦ
  have hkey := hC₀ _ (hPcd.of_le (by exact_mod_cast le_top))
    (Work.Diff.STE.periodization_periodic Φ)
  have hEt := ENormSq_periodization_le_of_compact hK hR hΦK hΦ t
  have hE0 := ENormSq_periodization_le_of_compact hK hR hΦK hΦ 0
  have hE1 : Work.Diff.STE.ENormSq t
        (fun z : ι → ℝ => ∑' m : ι → ℤ, Φ (z + Work.Diff.STE.iVec m))
      ≤ ((latBox ι ⌈R + 1 + 1⌉).card : ℝ) ^ 2 * T :=
    le_trans hEt (mul_le_mul_of_nonneg_left htT (by positivity))
  have hE2 : Work.Diff.STE.ENormSq 0
        (fun z : ι → ℝ => ∑' m : ι → ℤ, Φ (z + Work.Diff.STE.iVec m))
      ≤ ((latBox ι ⌈R + 1 + 1⌉).card : ℝ) ^ 2 * T :=
    le_trans hE0 (mul_le_mul_of_nonneg_left h0T (by positivity))
  calc Work.Diff.STE.CSq t (Work.Diff.STE.fourierCoeff
          (fun z : ι → ℝ => ∑' m : ι → ℤ, Φ (z + Work.Diff.STE.iVec m)))
      ≤ C₀ * (Work.Diff.STE.ENormSq t
            (fun z : ι → ℝ => ∑' m : ι → ℤ, Φ (z + Work.Diff.STE.iVec m))
          + Work.Diff.STE.ENormSq 0
            (fun z : ι → ℝ => ∑' m : ι → ℤ, Φ (z + Work.Diff.STE.iVec m))) := hkey
    _ ≤ C₀ * (((latBox ι ⌈R + 1 + 1⌉).card : ℝ) ^ 2 * T
          + ((latBox ι ⌈R + 1 + 1⌉).card : ℝ) ^ 2 * T) :=
        mul_le_mul_of_nonneg_left (add_le_add hE1 hE2) hC₀nn
    _ = C₀ * 2 * ((latBox ι ⌈R + 1 + 1⌉).card : ℝ) ^ 2 * T := by ring

end Work.Diff.STE.B3.SymCalcStep8
