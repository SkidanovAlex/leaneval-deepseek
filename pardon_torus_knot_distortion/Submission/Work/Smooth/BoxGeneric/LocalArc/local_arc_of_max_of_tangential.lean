import Mathlib
import Submission.Work.Smooth.BoxGeneric.LocalArc.exists_root_pair
import Submission.Work.Smooth.BoxGeneric.LocalArc.exists_isometric_linear_of_ne_zero

/-!
# The zero set of `max f g` near a common regular zero with equal tangential derivatives

Let `f g : ℝ × ℝ → ℝ` be `C¹`, let `p` be a common zero of `f` and `g`, and suppose that the two
derivatives at `p` agree and are nonzero.  Then near `p` the zero set
`{q | max (f q) (g q) = 0}` is a topological arc through `p`: it admits a continuous injective
parametrisation on the interval `(-1, 1)` whose image is exactly that zero set in a small ball
around `p`.

This is the *tangential* companion of `local_arc_of_max_of_isInvertible` (the transversality case,
where the pair `(f, g)` has invertible derivative at `p`).  Here the common derivative `L` is a
nonzero linear functional, so the two level curves `{f = 0}` and `{g = 0}` are tangent at `p`.
Writing the geometry in coordinates in which `L` is the first coordinate and `L (M (1,0)) > 0` for
an isometric linear `M` (`exists_isometric_linear_of_ne_zero`), both zero sets are graphs
`x = ψ y`, resp. `x = φ y`, of continuous functions over a common rectangle
(`exists_root_pair`), and the zero set of the maximum is the graph of `y ↦ min (φ y) (ψ y)`.
-/

open Set

namespace Work.Smooth.BoxGeneric.LocalArc

lemma max_eq_zero_iff {a b : ℝ} : max a b = 0 ↔ a ≤ 0 ∧ b ≤ 0 ∧ (a = 0 ∨ b = 0) := by
  constructor
  · intro h
    have ha : a ≤ 0 := le_trans (le_max_left a b) (le_of_eq h)
    have hb : b ≤ 0 := le_trans (le_max_right a b) (le_of_eq h)
    refine ⟨ha, hb, ?_⟩
    by_contra hc
    rw [not_or] at hc
    have hmax : max a b < 0 := max_lt (lt_of_le_of_ne ha hc.1) (lt_of_le_of_ne hb hc.2)
    rw [h] at hmax
    exact lt_irrefl 0 hmax
  · rintro ⟨ha, hb, h0 | h0⟩
    · rw [h0]; exact max_eq_left hb
    · rw [h0]; exact max_eq_right ha

lemma abs_min_le {a b c : ℝ} (ha : |a| ≤ c) (hb : |b| ≤ c) : |min a b| ≤ c := by
  rcases min_choice a b with h | h <;> rw [h] <;> assumption

lemma fderiv_comp_const_add_linear (f : ℝ × ℝ → ℝ) (hf : ContDiff ℝ 1 f) (p : ℝ × ℝ)
    (M : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) :
    fderiv ℝ (fun z : ℝ × ℝ => f (p + M z)) 0 = (fderiv ℝ f p).comp M := by
  have hM : HasFDerivAt (fun z : ℝ × ℝ => p + M z) M 0 :=
    (ContinuousLinearMap.hasFDerivAt M).const_add p
  have hfd : HasFDerivAt f (fderiv ℝ f p) p :=
    (hf.differentiable (by norm_num)).differentiableAt.hasFDerivAt
  have hfd' : HasFDerivAt f (fderiv ℝ f p) ((fun z : ℝ × ℝ => p + M z) 0) := by
    simpa using hfd
  exact (hfd'.comp 0 hM).fderiv

theorem local_arc_of_max_of_tangential_of_linear {f g : ℝ × ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    {p : ℝ × ℝ} (hfp : f p = 0) (hgp : g p = 0)
    (htang : fderiv ℝ f p = fderiv ℝ g p)
    (M : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (hiso : ∀ z, ‖M z‖ = ‖z‖)
    (hsurj : Function.Surjective M) (hpos : 0 < (fderiv ℝ f p) (M (1, 0))) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ ρ : ℝ → ℝ × ℝ, ρ 0 = p ∧ ContinuousOn ρ (Set.Ioo (-1 : ℝ) 1) ∧
      Set.InjOn ρ (Set.Ioo (-1 : ℝ) 1) ∧
      (∀ t ∈ Set.Ioo (-1 : ℝ) 1, max (f (ρ t)) (g (ρ t)) = 0) ∧
      (∀ q : ℝ × ℝ, max (f q) (g q) = 0 → ‖q - p‖ < ε → ∃ t ∈ Set.Ioo (-1 : ℝ) 1, ρ t = q) := by
  set F : ℝ × ℝ → ℝ := fun z => f (p + M z) with hFdef
  set G : ℝ × ℝ → ℝ := fun z => g (p + M z) with hGdef
  have hFcd : ContDiff ℝ 1 F := by rw [hFdef]; fun_prop
  have hGcd : ContDiff ℝ 1 G := by rw [hGdef]; fun_prop
  have hF0 : F 0 = 0 := by rw [hFdef]; simp [hfp]
  have hG0 : G 0 = 0 := by rw [hGdef]; simp [hgp]
  have hFtan : fderiv ℝ F 0 = fderiv ℝ G 0 := by
    rw [hFdef, hGdef, fderiv_comp_const_add_linear f hf p M,
      fderiv_comp_const_add_linear g hg p M, htang]
  have hFpos : 0 < (fderiv ℝ F 0) (1, 0) := by
    rw [hFdef, fderiv_comp_const_add_linear f hf p M]
    simpa using hpos
  have hGpos : 0 < (fderiv ℝ G 0) (1, 0) := by
    rw [hGdef, fderiv_comp_const_add_linear g hg p M, ← htang]
    simpa using hpos
  obtain ⟨Rx, Ry, hRx, hRy, ψ, φ, hψ0, hφ0, hψc, hφc, hroot, hle, heq⟩ :=
    exists_root_pair hFcd hGcd hF0 hG0 hFtan hFpos
  set ρ : ℝ → ℝ × ℝ := fun t => p + M (min (φ (Ry * t)) (ψ (Ry * t)), Ry * t) with hρdef
  refine ⟨min Rx Ry, lt_min hRx hRy, ρ, ?_, ?_, ?_, ?_, ?_⟩
  · show p + M (min (φ (Ry * 0)) (ψ (Ry * 0)), Ry * 0) = p
    rw [mul_zero, hφ0, hψ0, min_self]
    show p + M (0 : ℝ × ℝ) = p
    rw [map_zero, add_zero]
  · show ContinuousOn (fun t : ℝ => p + M (min (φ (Ry * t)) (ψ (Ry * t)), Ry * t))
      (Set.Ioo (-1 : ℝ) 1)
    have hmap : Set.MapsTo (fun t : ℝ => Ry * t) (Set.Ioo (-1 : ℝ) 1) (Set.Ioo (-Ry) Ry) := by
      intro t ht
      rw [Set.mem_Ioo] at ht ⊢
      constructor
      · have := mul_lt_mul_of_pos_left ht.1 hRy
        rwa [mul_neg, mul_one] at this
      · have := mul_lt_mul_of_pos_left ht.2 hRy
        rwa [mul_one] at this
    have hψ' : ContinuousOn (fun t : ℝ => ψ (Ry * t)) (Set.Ioo (-1 : ℝ) 1) :=
      hψc.comp (continuous_const.mul continuous_id).continuousOn hmap
    have hφ' : ContinuousOn (fun t : ℝ => φ (Ry * t)) (Set.Ioo (-1 : ℝ) 1) :=
      hφc.comp (continuous_const.mul continuous_id).continuousOn hmap
    have hmin : ContinuousOn (fun t : ℝ => min (φ (Ry * t)) (ψ (Ry * t))) (Set.Ioo (-1 : ℝ) 1) :=
      fun t ht => (hφ' t ht).min (hψ' t ht)
    have hpair : ContinuousOn (fun t : ℝ => (min (φ (Ry * t)) (ψ (Ry * t)), Ry * t))
        (Set.Ioo (-1 : ℝ) 1) :=
      hmin.prodMk (continuous_const.mul continuous_id).continuousOn
    exact (continuous_const.add M.continuous).comp_continuousOn hpair
  · show Set.InjOn (fun t : ℝ => p + M (min (φ (Ry * t)) (ψ (Ry * t)), Ry * t))
      (Set.Ioo (-1 : ℝ) 1)
    intro t1 ht1 t2 ht2 h
    have hM : M (min (φ (Ry * t1)) (ψ (Ry * t1)), Ry * t1)
        = M (min (φ (Ry * t2)) (ψ (Ry * t2)), Ry * t2) := add_left_cancel h
    have hσ : (min (φ (Ry * t1)) (ψ (Ry * t1)), Ry * t1)
        = (min (φ (Ry * t2)) (ψ (Ry * t2)), Ry * t2) := by
      have hnorm : ‖(min (φ (Ry * t1)) (ψ (Ry * t1)), Ry * t1)
          - (min (φ (Ry * t2)) (ψ (Ry * t2)), Ry * t2)‖ = 0 := by
        rw [← hiso ((min (φ (Ry * t1)) (ψ (Ry * t1)), Ry * t1)
          - (min (φ (Ry * t2)) (ψ (Ry * t2)), Ry * t2)), map_sub, hM, sub_self, norm_zero]
      exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
    have h2 : Ry * t1 = Ry * t2 := congrArg Prod.snd hσ
    exact mul_left_cancel₀ (ne_of_gt hRy) h2
  · show ∀ t ∈ Set.Ioo (-1 : ℝ) 1, max (f (p + M (min (φ (Ry * t)) (ψ (Ry * t)), Ry * t)))
      (g (p + M (min (φ (Ry * t)) (ψ (Ry * t)), Ry * t))) = 0
    intro t ht
    rw [Set.mem_Ioo] at ht
    have hyt : |Ry * t| < Ry := by
      rw [abs_mul, abs_of_pos hRy]
      have h1 : |t| < 1 := abs_lt.mpr ht
      nlinarith
    have hy_le : |Ry * t| ≤ Ry := le_of_lt hyt
    obtain ⟨hψb, hφb, hψr, hφr⟩ := hroot (Ry * t) hy_le
    have hx_le : |min (φ (Ry * t)) (ψ (Ry * t))| ≤ Rx := abs_min_le hφb hψb
    obtain ⟨hFle, hGle⟩ := hle (min (φ (Ry * t)) (ψ (Ry * t))) (Ry * t) hx_le hy_le
    obtain ⟨hFeq, hGeq⟩ := heq (min (φ (Ry * t)) (ψ (Ry * t))) (Ry * t) hx_le hy_le
    have hfρ : f (p + M (min (φ (Ry * t)) (ψ (Ry * t)), Ry * t))
        = F (min (φ (Ry * t)) (ψ (Ry * t)), Ry * t) := by rw [hFdef]
    have hgρ : g (p + M (min (φ (Ry * t)) (ψ (Ry * t)), Ry * t))
        = G (min (φ (Ry * t)) (ψ (Ry * t)), Ry * t) := by rw [hGdef]
    rw [hfρ, hgρ, max_eq_zero_iff]
    refine ⟨?_, ?_, ?_⟩
    · rw [hFle]; exact min_le_right _ _
    · rw [hGle]; exact min_le_left _ _
    · rcases min_choice (φ (Ry * t)) (ψ (Ry * t)) with hmin | hmin
      · right; rw [hmin]; exact hφr
      · left; rw [hmin]; exact hψr
  · intro q hq hqε
    obtain ⟨z, hz⟩ := hsurj (q - p)
    have hzn : ‖z‖ = ‖q - p‖ := by rw [← hiso z, hz]
    have hzle : ‖z‖ < min Rx Ry := by rw [hzn]; exact hqε
    have hz1 : |z.1| ≤ Rx := by
      have h1 : |z.1| ≤ ‖z‖ := by rw [Prod.norm_def]; exact le_max_left _ _
      calc |z.1| ≤ ‖z‖ := h1
        _ ≤ min Rx Ry := le_of_lt hzle
        _ ≤ Rx := min_le_left _ _
    have hz2 : |z.2| < Ry := by
      have h1 : |z.2| ≤ ‖z‖ := by rw [Prod.norm_def]; exact le_max_right _ _
      calc |z.2| ≤ ‖z‖ := h1
        _ < min Rx Ry := hzle
        _ ≤ Ry := min_le_right _ _
    have hz2le : |z.2| ≤ Ry := le_of_lt hz2
    have hqz : p + M z = q := by rw [hz]; abel
    have hfq : f q = F z := by rw [← hqz, hFdef]
    have hgq : g q = G z := by rw [← hqz, hGdef]
    rw [max_eq_zero_iff] at hq
    obtain ⟨hFle', hGle', hor⟩ := hq
    rw [hfq] at hFle'; rw [hgq] at hGle'; rw [hfq, hgq] at hor
    obtain ⟨hFle, hGle⟩ := hle z.1 z.2 hz1 hz2le
    obtain ⟨hFeq, hGeq⟩ := heq z.1 z.2 hz1 hz2le
    have hxz : z.1 = min (φ z.2) (ψ z.2) := by
      refine le_antisymm ?_ ?_
      · exact le_min (hGle.mp hGle') (hFle.mp hFle')
      · rcases hor with h | h
        · rw [(hFeq.mp h).symm]; exact min_le_right _ _
        · rw [(hGeq.mp h).symm]; exact min_le_left _ _
    refine ⟨z.2 / Ry, ?_, ?_⟩
    · rw [Set.mem_Ioo]
      constructor
      · rw [lt_div_iff₀ hRy]
        simpa using (abs_lt.mp hz2).1
      · rw [div_lt_one hRy]
        simpa using (abs_lt.mp hz2).2
    · show p + M (min (φ (Ry * (z.2 / Ry))) (ψ (Ry * (z.2 / Ry))), Ry * (z.2 / Ry)) = q
      rw [mul_div_cancel₀ z.2 (ne_of_gt hRy), ← hxz, hqz]

theorem local_arc_of_max_of_tangential {f g : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    {p : ℝ × ℝ} (hfp : f p = 0) (hgp : g p = 0)
    (htang : fderiv ℝ f p = fderiv ℝ g p) (hreg : fderiv ℝ f p ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ ρ : ℝ → ℝ × ℝ, ρ 0 = p ∧ ContinuousOn ρ (Set.Ioo (-1 : ℝ) 1) ∧
      Set.InjOn ρ (Set.Ioo (-1 : ℝ) 1) ∧
      (∀ t ∈ Set.Ioo (-1 : ℝ) 1, max (f (ρ t)) (g (ρ t)) = 0) ∧
      (∀ q : ℝ × ℝ, max (f q) (g q) = 0 → ‖q - p‖ < ε → ∃ t ∈ Set.Ioo (-1 : ℝ) 1, ρ t = q) := by
  obtain ⟨M, hiso, hsurj, hpos⟩ := exists_isometric_linear_of_ne_zero (fderiv ℝ f p) hreg
  exact local_arc_of_max_of_tangential_of_linear hf hg hfp hgp htang M hiso hsurj hpos
end Work.Smooth.BoxGeneric.LocalArc
