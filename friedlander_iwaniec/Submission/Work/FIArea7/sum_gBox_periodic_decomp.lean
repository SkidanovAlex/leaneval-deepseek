import Mathlib
import Submission.Work.FIArea7.card_Icc_int_filter_mod_eq
import Submission.Work.FIArea7.FIsymbols

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea7

/-- **The "elementary counting" of *FI* Lemma 21.2: a periodic function summed over the box.**  For
`q > 0` and `F : ZMod q → ZMod q → ℂ` with `‖F‖ ≤ 1`, the sum of `F` over the box
`gBox R = {|Re|,|Im| ≤ R}` is its sum over a complete residue system, scaled by the average number
`A = ⌊(2R+1)/q⌋` of representatives per class, up to an error:

  `Σ_{z ∈ gBox R} F(z mod q) = A²·Σ_{ζ ∈ (Z/q)²} F(ζ) + E`,  `‖E‖ ≤ 2((2R+1)·q + q²)`.

Writing `c_u = #{a ∈ [−R,R] : a ≡ u (mod q)} = A + θ_u` with `θ_u ∈ {0,1}`
(`Work.FIArea7.card_Icc_int_filter_mod_eq`), the identity is
`Σ_{u,v}(A+θ_u)(A+θ_v)F(u,v) = A²ΣF + A·Σ(θ_u+θ_v)F + Σθ_uθ_v F`, and `‖F‖ ≤ 1` gives
`|Σ_{u,v}(θ_u+θ_v)F| ≤ 2q²`, `|Σθ_uθ_vF| ≤ q²`; `A·q ≤ 2R+1`.

This is the step *"Splitting the inner summation into residue classes `ζ (mod q)` … by elementary
counting"* in the proof of Lemma 21.1/21.2 of *FI* §21, and it is used with `F = ξ_{w₁}(·)ξ_{w₂}(·)`
so that the main term is the exact orthogonality value `Work.FIArea7.sum_xiC_general`. -/
theorem sum_gBox_periodic_decomp (R : ℤ) (q : ℕ) [NeZero q] (F : ZMod q → ZMod q → ℂ)
    (hF : ∀ u v, ‖F u v‖ ≤ 1) :
    ∃ E : ℂ, ‖E‖ ≤ 2 * ((((2 * R + 1).toNat : ℝ) * (q : ℝ)) + (q : ℝ) ^ 2) ∧
      (∑ z ∈ Work.FIPlan.gBox R, F (z.re : ZMod q) (z.im : ZMod q))
        = ((((2 * R + 1).toNat / q : ℕ) : ℂ)) ^ 2
            * (∑ u : ZMod q, ∑ v : ZMod q, F u v) + E := by
  classical
  -- `A = ⌊(2R+1)/q⌋` is the average number of representatives per residue class, and `cnt u`
  -- is the exact number of `a ∈ [−R,R]` with `a ≡ u (mod q)`.
  set A : ℕ := (2 * R + 1).toNat / q with hA
  set cnt : ZMod q → ℕ :=
    fun u => ((Finset.Icc (-R) R).filter (fun a : ℤ => (a : ZMod q) = u)).card with hcnt
  -- `cnt u = A + θ u` with `θ u ∈ {0,1}`, by the exact residue-class count.
  have hex : ∀ u : ZMod q, ∃ θ : ℕ, θ ≤ 1 ∧ cnt u = A + θ := by
    intro u
    obtain ⟨θ, h1, h2⟩ := card_Icc_int_filter_mod_eq R q (Nat.pos_of_neZero q) u
    refine ⟨θ, h1, ?_⟩
    rw [hA]
    simp only [hcnt]
    exact h2
  choose θ hθ using hex
  -- Step 1: replace the sum over the box `gBox R` by a double sum over `[−R,R]²`.
  have hbox : (∑ z ∈ Work.FIPlan.gBox R, F (z.re : ZMod q) (z.im : ZMod q))
      = ∑ a ∈ Finset.Icc (-R) R, ∑ b ∈ Finset.Icc (-R) R, F (a : ZMod q) (b : ZMod q) := by
    rw [Work.FIPlan.gBox, Finset.sum_image (by intro p _ p' _ h; exact Work.FIPlan.gaussMk_injective h)]
    exact Finset.sum_product (Finset.Icc (-R) R) (Finset.Icc (-R) R)
      (fun x => F ((⟨x.1, x.2⟩ : GaussianInt).re : ZMod q) ((⟨x.1, x.2⟩ : GaussianInt).im : ZMod q))
  -- Step 2: group a one-variable sum by residue class.
  have hgroup : ∀ G : ZMod q → ℂ,
      ∑ a ∈ Finset.Icc (-R) R, G (a : ZMod q) = ∑ u : ZMod q, (cnt u : ℂ) * G u := by
    intro G
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.Icc (-R) R) (t := Finset.univ)
        (g := fun a : ℤ => (a : ZMod q)) (by intro i _; exact Finset.mem_univ _)
        (fun a => G (a : ZMod q))]
    apply Finset.sum_congr rfl
    intro u _
    have h1 : ((Finset.Icc (-R) R).filter (fun a : ℤ => (a : ZMod q) = u)).sum
          (fun a => G (a : ZMod q))
        = ((Finset.Icc (-R) R).filter (fun a : ℤ => (a : ZMod q) = u)).sum (fun _ => G u) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mem_filter] at ha
      rw [ha.2]
    rw [h1, Finset.sum_const, nsmul_eq_mul]
  -- Step 3: the box sum is the doubly residue-class-grouped sum.
  have hdouble : ∑ a ∈ Finset.Icc (-R) R, ∑ b ∈ Finset.Icc (-R) R, F (a : ZMod q) (b : ZMod q)
      = ∑ u : ZMod q, ∑ v : ZMod q, (cnt u : ℂ) * (cnt v : ℂ) * F u v := by
    rw [hgroup (fun u => ∑ b ∈ Finset.Icc (-R) R, F u (b : ZMod q))]
    apply Finset.sum_congr rfl
    intro u _
    rw [hgroup (fun v => F u v), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring
  -- Step 4: split `(A+θ_u)(A+θ_v)` and identify the main term and the error.
  have hdecomp : ∀ u v : ZMod q, (cnt u : ℂ) * (cnt v : ℂ) * F u v
      = (A : ℂ)^2 * F u v + (A : ℂ) * (((θ u : ℂ) + (θ v : ℂ)) * F u v)
        + ((θ u : ℂ) * (θ v : ℂ)) * F u v := by
    intro u v
    have hu : (cnt u : ℂ) = (A : ℂ) + (θ u : ℂ) := by
      rw [show cnt u = A + θ u from (hθ u).2]; push_cast; ring
    have hv : (cnt v : ℂ) = (A : ℂ) + (θ v : ℂ) := by
      rw [show cnt v = A + θ v from (hθ v).2]; push_cast; ring
    rw [hu, hv]; ring
  have key : ∑ u : ZMod q, ∑ v : ZMod q, (cnt u : ℂ) * (cnt v : ℂ) * F u v
      = (A : ℂ)^2 * (∑ u : ZMod q, ∑ v : ZMod q, F u v)
        + ((A : ℂ) * (∑ u : ZMod q, ∑ v : ZMod q, ((θ u : ℂ) + (θ v : ℂ)) * F u v)
           + (∑ u : ZMod q, ∑ v : ZMod q, ((θ u : ℂ) * (θ v : ℂ)) * F u v)) := by
    have hP : (∑ u : ZMod q, ∑ v : ZMod q, (A : ℂ)^2 * F u v)
        = (A : ℂ)^2 * (∑ u, ∑ v, F u v) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro u _
      rw [Finset.mul_sum]
    have hQ : (∑ u : ZMod q, ∑ v : ZMod q, (A : ℂ) * (((θ u : ℂ) + (θ v : ℂ)) * F u v))
        = (A : ℂ) * (∑ u, ∑ v, ((θ u : ℂ) + (θ v : ℂ)) * F u v) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro u _
      rw [Finset.mul_sum]
    have step : (∑ u : ZMod q, ∑ v : ZMod q, (cnt u : ℂ) * (cnt v : ℂ) * F u v)
        = ∑ u : ZMod q, ∑ v : ZMod q, ((A : ℂ)^2 * F u v
            + (A : ℂ) * (((θ u : ℂ) + (θ v : ℂ)) * F u v)
            + ((θ u : ℂ) * (θ v : ℂ)) * F u v) := by
      apply Finset.sum_congr rfl; intro u _
      apply Finset.sum_congr rfl; intro v _
      exact hdecomp u v
    rw [step]
    simp only [Finset.sum_add_distrib]
    rw [hP, hQ]
    ring
  -- Step 5: the two error terms are bounded by `2q²` and `q²`.
  have hT1 : ‖∑ u : ZMod q, ∑ v : ZMod q, ((θ u : ℂ) + (θ v : ℂ)) * F u v‖
      ≤ 2 * (q : ℝ)^2 := by
    have hsum1 : ‖∑ u : ZMod q, ∑ v : ZMod q, ((θ u : ℂ) + (θ v : ℂ)) * F u v‖
        ≤ ∑ u : ZMod q, ∑ v : ZMod q, ((θ u : ℝ) + (θ v : ℝ)) := by
      calc ‖∑ u : ZMod q, ∑ v : ZMod q, ((θ u : ℂ) + (θ v : ℂ)) * F u v‖
          ≤ ∑ u : ZMod q, ‖∑ v : ZMod q, ((θ u : ℂ) + (θ v : ℂ)) * F u v‖ := norm_sum_le _ _
        _ ≤ ∑ u : ZMod q, ∑ v : ZMod q, ‖((θ u : ℂ) + (θ v : ℂ)) * F u v‖ := by
            apply Finset.sum_le_sum; intro u _
            exact norm_sum_le _ _
        _ = ∑ u : ZMod q, ∑ v : ZMod q, ((θ u : ℝ) + (θ v : ℝ)) * ‖F u v‖ := by
            apply Finset.sum_congr rfl; intro u _
            apply Finset.sum_congr rfl; intro v _
            rw [norm_mul]
            congr 1
            have hc : (θ u : ℂ) + (θ v : ℂ) = ((θ u + θ v : ℕ) : ℂ) := by push_cast; ring
            rw [hc, Complex.norm_natCast]
            push_cast; ring
        _ ≤ ∑ u : ZMod q, ∑ v : ZMod q, ((θ u : ℝ) + (θ v : ℝ)) := by
            apply Finset.sum_le_sum; intro u _
            apply Finset.sum_le_sum; intro v _
            have hnn : (0 : ℝ) ≤ (θ u : ℝ) + (θ v : ℝ) := by positivity
            have := mul_le_mul_of_nonneg_left (hF u v) hnn
            simpa using this
    have hstep : ∑ u : ZMod q, ∑ v : ZMod q, ((θ u : ℝ) + (θ v : ℝ))
        ≤ ∑ u : ZMod q, ∑ v : ZMod q, (2 : ℝ) := by
      apply Finset.sum_le_sum; intro u _
      apply Finset.sum_le_sum; intro v _
      have hu : (θ u : ℝ) ≤ 1 := by exact_mod_cast (hθ u).1
      have hv : (θ v : ℝ) ≤ 1 := by exact_mod_cast (hθ v).1
      linarith
    have hfin : (∑ u : ZMod q, ∑ v : ZMod q, (2 : ℝ)) = 2 * (q : ℝ)^2 := by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ZMod.card]
      ring
    calc ‖∑ u : ZMod q, ∑ v : ZMod q, ((θ u : ℂ) + (θ v : ℂ)) * F u v‖
        ≤ ∑ u : ZMod q, ∑ v : ZMod q, ((θ u : ℝ) + (θ v : ℝ)) := hsum1
      _ ≤ ∑ u : ZMod q, ∑ v : ZMod q, (2 : ℝ) := hstep
      _ = 2 * (q : ℝ)^2 := hfin
  have hT2 : ‖∑ u : ZMod q, ∑ v : ZMod q, ((θ u : ℂ) * (θ v : ℂ)) * F u v‖
      ≤ (q : ℝ)^2 := by
    have hsum1 : ‖∑ u : ZMod q, ∑ v : ZMod q, ((θ u : ℂ) * (θ v : ℂ)) * F u v‖
        ≤ ∑ u : ZMod q, ∑ v : ZMod q, ((θ u : ℝ) * (θ v : ℝ)) := by
      calc ‖∑ u : ZMod q, ∑ v : ZMod q, ((θ u : ℂ) * (θ v : ℂ)) * F u v‖
          ≤ ∑ u : ZMod q, ‖∑ v : ZMod q, ((θ u : ℂ) * (θ v : ℂ)) * F u v‖ := norm_sum_le _ _
        _ ≤ ∑ u : ZMod q, ∑ v : ZMod q, ‖((θ u : ℂ) * (θ v : ℂ)) * F u v‖ := by
            apply Finset.sum_le_sum; intro u _
            exact norm_sum_le _ _
        _ = ∑ u : ZMod q, ∑ v : ZMod q, ((θ u : ℝ) * (θ v : ℝ)) * ‖F u v‖ := by
            apply Finset.sum_congr rfl; intro u _
            apply Finset.sum_congr rfl; intro v _
            rw [norm_mul]
            congr 1
            have hc : (θ u : ℂ) * (θ v : ℂ) = ((θ u * θ v : ℕ) : ℂ) := by push_cast; ring
            rw [hc, Complex.norm_natCast]
            push_cast; ring
        _ ≤ ∑ u : ZMod q, ∑ v : ZMod q, ((θ u : ℝ) * (θ v : ℝ)) := by
            apply Finset.sum_le_sum; intro u _
            apply Finset.sum_le_sum; intro v _
            have hnn : (0 : ℝ) ≤ (θ u : ℝ) * (θ v : ℝ) := by positivity
            have := mul_le_mul_of_nonneg_left (hF u v) hnn
            simpa using this
    have hstep : ∑ u : ZMod q, ∑ v : ZMod q, ((θ u : ℝ) * (θ v : ℝ))
        ≤ ∑ u : ZMod q, ∑ v : ZMod q, (1 : ℝ) := by
      apply Finset.sum_le_sum; intro u _
      apply Finset.sum_le_sum; intro v _
      have hu : (θ u : ℝ) ≤ 1 := by exact_mod_cast (hθ u).1
      have hv : (θ v : ℝ) ≤ 1 := by exact_mod_cast (hθ v).1
      have hu0 : (0 : ℝ) ≤ θ u := by positivity
      have hv0 : (0 : ℝ) ≤ θ v := by positivity
      nlinarith [hu, hv, hu0, hv0]
    have hfin : (∑ u : ZMod q, ∑ v : ZMod q, (1 : ℝ)) = (q : ℝ)^2 := by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ZMod.card]
      ring
    calc ‖∑ u : ZMod q, ∑ v : ZMod q, ((θ u : ℂ) * (θ v : ℂ)) * F u v‖
        ≤ ∑ u : ZMod q, ∑ v : ZMod q, ((θ u : ℝ) * (θ v : ℝ)) := hsum1
      _ ≤ ∑ u : ZMod q, ∑ v : ZMod q, (1 : ℝ) := hstep
      _ = (q : ℝ)^2 := hfin
  refine ⟨(A : ℂ) * (∑ u : ZMod q, ∑ v : ZMod q, ((θ u : ℂ) + (θ v : ℂ)) * F u v)
      + (∑ u : ZMod q, ∑ v : ZMod q, ((θ u : ℂ) * (θ v : ℂ)) * F u v), ?_, ?_⟩
  · -- Bound `‖E‖ ≤ A·2q² + q² ≤ 2((2R+1)q + q²)`, using `A·q ≤ (2R+1).toNat`.
    have hq0 : (0 : ℝ) ≤ (q : ℝ) := by positivity
    have hAq : (A : ℝ) * (q : ℝ) ≤ ((2 * R + 1).toNat : ℝ) := by
      rw [hA]; exact_mod_cast Nat.div_mul_le_self (2 * R + 1).toNat q
    calc ‖(A : ℂ) * (∑ u : ZMod q, ∑ v : ZMod q, ((θ u : ℂ) + (θ v : ℂ)) * F u v)
          + (∑ u : ZMod q, ∑ v : ZMod q, ((θ u : ℂ) * (θ v : ℂ)) * F u v)‖
        ≤ ‖(A : ℂ) * (∑ u : ZMod q, ∑ v : ZMod q, ((θ u : ℂ) + (θ v : ℂ)) * F u v)‖
          + ‖(∑ u : ZMod q, ∑ v : ZMod q, ((θ u : ℂ) * (θ v : ℂ)) * F u v)‖ := norm_add_le _ _
      _ = (A : ℝ) * ‖∑ u : ZMod q, ∑ v : ZMod q, ((θ u : ℂ) + (θ v : ℂ)) * F u v‖
          + ‖∑ u : ZMod q, ∑ v : ZMod q, ((θ u : ℂ) * (θ v : ℂ)) * F u v‖ := by
            rw [norm_mul, Complex.norm_natCast]
      _ ≤ (A : ℝ) * (2 * (q : ℝ)^2) + (q : ℝ)^2 := by
            have h1 := mul_le_mul_of_nonneg_left hT1 (by positivity : (0 : ℝ) ≤ A)
            linarith [hT2]
      _ ≤ 2 * ((((2 * R + 1).toNat : ℝ) * (q : ℝ)) + (q : ℝ) ^ 2) := by
            nlinarith [hAq, hq0]
  · rw [show (∑ z ∈ Work.FIPlan.gBox R, F (z.re : ZMod q) (z.im : ZMod q))
        = ∑ a ∈ Finset.Icc (-R) R, ∑ b ∈ Finset.Icc (-R) R, F (a : ZMod q) (b : ZMod q) from hbox,
      hdouble, key, hA]

end Work.FIArea7
