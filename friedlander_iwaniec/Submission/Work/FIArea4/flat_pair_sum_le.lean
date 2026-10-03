import Mathlib
import Submission.Work.FIArea4.Vflip.card_sq_filter_le

/-!
# The flat pair sum bound (`Work.FIArea4.flat_pair_sum_le`)

For `E : ℕ → ℝ` with `E d ≥ 0` and `D ≥ 1`,

`∑_{d₁ ∈ (D,2D]} ∑_{d₂ ∈ (D,2D], d₁' d₂' = □} √(E d₁ E d₂) ≤ √(2D) · ∑_{d ∈ (D,2D]} E d`,

where `d' = oddPart d` denotes the odd part (`Work.FIPlan.oddPart`).

The flat condition `d₁' d₂' = □` on `d₁, d₂ ∈ (D,2D]` is equivalent
(`sqrt_sq_iff_kernel`) to the equality of the squarefree kernels
`sqfreeKernel d₁' = sqfreeKernel d₂'` of the odd parts.  Grouping the double sum into the fibers
of the map `d ↦ sqfreeKernel (oddPart d)` therefore rewrites it as
`∑_k (∑_{d ∈ fiber k} √(E d))²`; Cauchy–Schwarz in each fiber and the count
`|fiber k| ≤ √(2D)` of `Submission.Work.FIArea4.Vflip.card_sq_filter_le` finish the job.

The regrouping and the Cauchy–Schwarz step are abstracted in `fiber_cs_le`.
-/

namespace Work.FIArea4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- If `a, b ≥ 1` have equal squarefree kernels then `a * b` is a perfect square. -/
private lemma mul_sq_of_kernel_eq {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : Work.FIArea4.sqfreeKernel a = Work.FIArea4.sqfreeKernel b) :
    ∃ m : ℕ, a * b = m ^ 2 := by
  obtain ⟨-, -, hma, -, -⟩ := Work.FIArea4.sqfree_kernel a (by omega)
  obtain ⟨-, -, hmb, -, -⟩ := Work.FIArea4.sqfree_kernel b (by omega)
  refine ⟨Work.FIArea4.sqfreeKernel a * Work.FIArea4.sqPart a * Work.FIArea4.sqPart b, ?_⟩
  have key : a * b = Work.FIArea4.sqfreeKernel a * Work.FIArea4.sqPart a ^ 2
      * (Work.FIArea4.sqfreeKernel b * Work.FIArea4.sqPart b ^ 2) := by
    rw [hma, hmb]
  rw [key, h]
  ring

/-- For `a, b ≥ 1`: `a * b` is a perfect square (in the `Nat.sqrt` normal form) iff `a` and `b`
have the same squarefree kernel.  This identifies the flat condition of the paper with the fibers
of the squarefree kernel. -/
private lemma sqrt_sq_iff_kernel {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (Nat.sqrt (a * b) ^ 2 = a * b) ↔ Work.FIArea4.sqfreeKernel a = Work.FIArea4.sqfreeKernel b := by
  constructor
  · intro h
    exact Work.FIArea4.sqfreeKernel_eq_of_mul_sq a b ha hb ⟨Nat.sqrt (a * b), h.symm⟩
  · intro h
    obtain ⟨m, hm⟩ := mul_sq_of_kernel_eq ha hb h
    rw [hm, Nat.sqrt_eq']

/-- **Fiber regrouping plus Cauchy–Schwarz.**  For a finite set `I` of naturals, a map `φ` and a
nonnegative weight `a` whose square is the function of interest, if every fiber of `φ` over
`I.image φ` has at most `r` elements then

`∑_{d₁ ∈ I} a d₁ · ∑_{d₂ ∈ I, φ d₂ = φ d₁} a d₂ ≤ r · ∑_{d ∈ I} a d ^ 2`.

The left side is `∑_k (∑_{d ∈ fiber k} a d)²` after regrouping, and each fiber term is bound by
Cauchy–Schwarz together with the cardinality bound `|fiber k| ≤ r`. -/
private lemma fiber_cs_le {I : Finset ℕ} {φ : ℕ → ℕ} {a : ℕ → ℝ} {r : ℝ}
    (_ha : ∀ d, 0 ≤ a d) (_hr : 0 ≤ r)
    (hcard : ∀ k ∈ I.image φ, ((I.filter (fun d => φ d = k)).card : ℝ) ≤ r) :
    ∑ d1 ∈ I, a d1 * (∑ d2 ∈ I.filter (fun d2 => φ d2 = φ d1), a d2)
      ≤ r * ∑ d ∈ I, a d ^ 2 := by
  have hmap : ∀ d1 ∈ I, φ d1 ∈ I.image φ := fun d1 hd1 => Finset.mem_image_of_mem φ hd1
  have hgroup : (∑ d1 ∈ I, a d1 * (∑ d2 ∈ I.filter (fun d2 => φ d2 = φ d1), a d2))
      = ∑ k ∈ I.image φ, (∑ d ∈ I.filter (fun d => φ d = k), a d) ^ 2 := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := I) (t := I.image φ) (g := φ) hmap
        (fun d1 => a d1 * (∑ d2 ∈ I.filter (fun d2 => φ d2 = φ d1), a d2))]
    apply Finset.sum_congr rfl
    intro k hk
    have hinner : ∀ d1 ∈ I.filter (fun d1 => φ d1 = k),
        a d1 * (∑ d2 ∈ I.filter (fun d2 => φ d2 = φ d1), a d2)
          = a d1 * (∑ d2 ∈ I.filter (fun d => φ d = k), a d2) := by
      intro d1 hd1
      rw [(Finset.mem_filter.mp hd1).2]
    rw [Finset.sum_congr rfl hinner, pow_two, ← Finset.sum_mul]
  calc (∑ d1 ∈ I, a d1 * (∑ d2 ∈ I.filter (fun d2 => φ d2 = φ d1), a d2))
      = ∑ k ∈ I.image φ, (∑ d ∈ I.filter (fun d => φ d = k), a d) ^ 2 := hgroup
    _ ≤ ∑ k ∈ I.image φ, r * ∑ d ∈ I.filter (fun d => φ d = k), a d ^ 2 := by
        apply Finset.sum_le_sum
        intro k hk
        have hCS := Finset.sum_mul_sq_le_sq_mul_sq (I.filter (fun d => φ d = k))
          (fun _ => (1:ℝ)) a
        simp only [one_mul, one_pow] at hCS
        have hcard1 : (∑ _x ∈ I.filter (fun d => φ d = k), (1:ℝ))
            = ((I.filter (fun d => φ d = k)).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        rw [hcard1] at hCS
        have hnn : (0:ℝ) ≤ ∑ d ∈ I.filter (fun d => φ d = k), a d ^ 2 :=
          Finset.sum_nonneg (fun d _ => by positivity)
        calc (∑ d ∈ I.filter (fun d => φ d = k), a d) ^ 2
            ≤ ((I.filter (fun d => φ d = k)).card : ℝ) *
                ∑ d ∈ I.filter (fun d => φ d = k), a d ^ 2 := hCS
          _ ≤ r * ∑ d ∈ I.filter (fun d => φ d = k), a d ^ 2 :=
              mul_le_mul_of_nonneg_right (hcard k hk) hnn
    _ = r * ∑ d ∈ I, a d ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_fiberwise_of_maps_to (s := I) (t := I.image φ) (g := φ)
          hmap (fun d => a d ^ 2)]

lemma flat_pair_sum_le (D : ℕ) (hD : 1 ≤ D) (E : ℕ → ℝ) (hE : ∀ d, 0 ≤ E d) :
    ∑ d1 ∈ Finset.Ioc D (2 * D),
        ∑ d2 ∈ (Finset.Ioc D (2 * D)).filter (fun d2 =>
            Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2
              = Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
          Real.sqrt (E d1 * E d2)
      ≤ Real.sqrt (2 * D) * ∑ d ∈ Finset.Ioc D (2 * D), E d := by
  set I : Finset ℕ := Finset.Ioc D (2 * D) with hI
  -- `oddPart d ≥ 1` for `d` in the dyadic interval
  have hpos : ∀ d ∈ I, 1 ≤ Work.FIPlan.oddPart d := by
    intro d hd
    rw [hI] at hd
    have hd1 : 1 ≤ d := by
      have := (Finset.mem_Ioc.mp hd).1
      omega
    have := Work.FIArea4.Vflip.oddPart_pos' (d := d) (by omega : d ≠ 0)
    omega
  -- every fiber of the squarefree kernel of the odd part has at most `√(2D)` elements
  have hker : ∀ k ∈ I.image (fun d => Work.FIArea4.sqfreeKernel (Work.FIPlan.oddPart d)),
      ((I.filter (fun d => Work.FIArea4.sqfreeKernel (Work.FIPlan.oddPart d) = k)).card : ℝ)
        ≤ Real.sqrt (2 * D) := by
    intro k hk
    obtain ⟨d0, hd0I, hd0k⟩ := Finset.mem_image.mp hk
    have hd0pos : 1 ≤ d0 := by
      rw [hI] at hd0I
      have := (Finset.mem_Ioc.mp hd0I).1
      omega
    have hset : I.filter (fun d => Work.FIArea4.sqfreeKernel (Work.FIPlan.oddPart d) = k)
        = I.filter (fun d => Nat.sqrt (Work.FIPlan.oddPart d0 * Work.FIPlan.oddPart d) ^ 2
            = Work.FIPlan.oddPart d0 * Work.FIPlan.oddPart d) := by
      apply Finset.filter_congr
      intro d hd
      rw [← hd0k]
      exact ((sqrt_sq_iff_kernel (hpos d0 hd0I) (hpos d hd)).trans eq_comm).symm
    rw [hset, hI]
    exact Work.FIArea4.Vflip.card_sq_filter_le D d0 hD hd0pos
  -- rewrite the double sum as `∑_{d₁} √(E d₁) · ∑_{d₂ : flat} √(E d₂)`
  have h1 : (∑ d1 ∈ I, ∑ d2 ∈ I.filter (fun d2 =>
        Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2
          = Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2), Real.sqrt (E d1 * E d2))
      = ∑ d1 ∈ I, Real.sqrt (E d1) * (∑ d2 ∈ I.filter (fun d2 =>
          Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2
            = Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2), Real.sqrt (E d2)) := by
    apply Finset.sum_congr rfl; intro d1 hd1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro d2 _
    rw [Real.sqrt_mul (hE d1)]
  -- replace the flat condition by equality of the squarefree kernels
  have h2 : (∑ d1 ∈ I, Real.sqrt (E d1) * (∑ d2 ∈ I.filter (fun d2 =>
          Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2
            = Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2), Real.sqrt (E d2)))
      = ∑ d1 ∈ I, Real.sqrt (E d1) * (∑ d2 ∈ I.filter (fun d2 =>
          Work.FIArea4.sqfreeKernel (Work.FIPlan.oddPart d2)
            = Work.FIArea4.sqfreeKernel (Work.FIPlan.oddPart d1)), Real.sqrt (E d2)) := by
    apply Finset.sum_congr rfl; intro d1 hd1
    have hf : I.filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2
            = Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2)
        = I.filter (fun d2 => Work.FIArea4.sqfreeKernel (Work.FIPlan.oddPart d2)
            = Work.FIArea4.sqfreeKernel (Work.FIPlan.oddPart d1)) := by
      apply Finset.filter_congr
      intro d2 hd2
      exact (sqrt_sq_iff_kernel (hpos d1 hd1) (hpos d2 hd2)).trans eq_comm
    rw [hf]
  have hmain := fiber_cs_le (I := I)
      (φ := fun d => Work.FIArea4.sqfreeKernel (Work.FIPlan.oddPart d))
      (a := fun d => Real.sqrt (E d)) (r := Real.sqrt (2 * D))
      (fun d => Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hker
  calc (∑ d1 ∈ I, ∑ d2 ∈ I.filter (fun d2 =>
        Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2
          = Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2), Real.sqrt (E d1 * E d2))
      = ∑ d1 ∈ I, Real.sqrt (E d1) * (∑ d2 ∈ I.filter (fun d2 =>
          Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2
            = Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2), Real.sqrt (E d2)) := h1
    _ = ∑ d1 ∈ I, Real.sqrt (E d1) * (∑ d2 ∈ I.filter (fun d2 =>
          Work.FIArea4.sqfreeKernel (Work.FIPlan.oddPart d2)
            = Work.FIArea4.sqfreeKernel (Work.FIPlan.oddPart d1)), Real.sqrt (E d2)) := h2
    _ ≤ Real.sqrt (2 * D) * ∑ d ∈ I, Real.sqrt (E d) ^ 2 := hmain
    _ = Real.sqrt (2 * D) * ∑ d ∈ I, E d := by
        congr 1
        apply Finset.sum_congr rfl; intro d _
        exact Real.sq_sqrt (hE d)

end

end Work.FIArea4
