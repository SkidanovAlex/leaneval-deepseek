import Mathlib
import Submission.Work.FIArea5.S16.poisson_helpers

namespace Work.FIArea5.S16

/-- The bijection `ℤ × ℤ ≃ (Fin q × Fin q) × (ℤ × ℤ)` sending `(n, m)` to the pair of
residue classes `(n mod q, m mod q)` together with the quotients `(n / q, m / q)`. -/
noncomputable def classEquiv (q : ℕ) (hq : 0 < q) : ℤ × ℤ ≃ (Fin q × Fin q) × (ℤ × ℤ) :=
  (Equiv.prodCongr (intResEquiv q hq) (intResEquiv q hq)).trans
    (Equiv.prodProdProdComm (Fin q) ℤ (Fin q) ℤ)

lemma classEquiv_symm_apply (q : ℕ) (hq : 0 < q) (a1 a2 : Fin q) (k l : ℤ) :
    (classEquiv q hq).symm ((a1, a2), (k, l)) =
      ((q : ℤ) * k + (a1 : ℤ), (q : ℤ) * l + (a2 : ℤ)) := by
  simp [classEquiv, Equiv.prodProdProdComm, Equiv.prodCongr, intResEquiv]

/-- A `q`-lattice shift of a summable sequence over `ℤ` is summable. -/
lemma summable_shift (q : ℕ) (hq : 0 < q) (F : ℤ → ℂ) (hF : Summable F) (a : ℤ) :
    Summable (fun k : ℤ => F ((q : ℤ) * k + a)) := by
  have hinj : Function.Injective (fun k : ℤ => (q : ℤ) * k + a) := by
    intro x y hxy
    have hq' : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
    have h : (q : ℤ) * x = (q : ℤ) * y := by linarith
    exact mul_left_cancel₀ hq' h
  simpa only [Function.comp_def] using hF.comp_injective hinj

/-- Joint summability of the `(Fin q × Fin q) × (ℤ × ℤ)`-indexed summand. -/
lemma summable_class_summand (q : ℕ) (hq : 0 < q) (g : GaussianInt → ℂ) (F H : ℤ → ℂ)
    (hF : Summable F) (hH : Summable H) :
    Summable (fun c : (Fin q × Fin q) × (ℤ × ℤ) =>
      g ⟨(c.1.1 : ℤ), (c.1.2 : ℤ)⟩ *
        (F ((q : ℤ) * c.2.1 + (c.1.1 : ℤ)) * H ((q : ℤ) * c.2.2 + (c.1.2 : ℤ)))) := by
  rw [← summable_norm_iff]
  rw [summable_prod_of_nonneg (fun _ => norm_nonneg _)]
  constructor
  · rintro ⟨a1, a2⟩
    have h1 : Summable (fun k : ℤ => ‖F ((q : ℤ) * k + (a1 : ℤ))‖) :=
      summable_norm_iff.mpr (summable_shift q hq F hF (a1 : ℤ))
    have h2 : Summable (fun l : ℤ => ‖H ((q : ℤ) * l + (a2 : ℤ))‖) :=
      summable_norm_iff.mpr (summable_shift q hq H hH (a2 : ℤ))
    have h3 : Summable (fun B : ℤ × ℤ =>
        ‖F ((q : ℤ) * B.1 + (a1 : ℤ))‖ * ‖H ((q : ℤ) * B.2 + (a2 : ℤ))‖) :=
      Summable.mul_of_nonneg h1 h2 (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    simpa only [norm_mul] using h3.mul_left ‖g ⟨(a1 : ℤ), (a2 : ℤ)⟩‖
  · exact Summable.of_finite

/-- The two-dimensional sum over a product of two `q`-lattices factors. -/
lemma tsum_prod_shift (q : ℕ) (hq : 0 < q) (F H : ℤ → ℂ) (hF : Summable F)
    (hH : Summable H) (a b : ℤ) :
    (∑' B : ℤ × ℤ, F ((q : ℤ) * B.1 + a) * H ((q : ℤ) * B.2 + b))
      = (∑' k : ℤ, F ((q : ℤ) * k + a)) * (∑' l : ℤ, H ((q : ℤ) * l + b)) := by
  rw [tsum_mul_tsum_of_summable_norm
      (f := fun k : ℤ => F ((q : ℤ) * k + a)) (g := fun l : ℤ => H ((q : ℤ) * l + b))
      (summable_norm_iff.mpr (summable_shift q hq F hF a))
      (summable_norm_iff.mpr (summable_shift q hq H hH b))]

/-- The `Fin q`-indexed form of the residue-class decomposition of the double sum. -/
theorem tsum_class_2d_fin (q : ℕ) (hq : 0 < q) (g : GaussianInt → ℂ)
    (hg : ∀ z w : GaussianInt, (((q : ℤ) : GaussianInt) ∣ (z - w)) → g z = g w)
    (F H : ℤ → ℂ) (hF : Summable fun n : ℤ => F n) (hH : Summable fun n : ℤ => H n) :
    (∑' z : ℤ × ℤ, g ⟨z.1, z.2⟩ * (F z.1 * H z.2))
      = ∑ a1 : Fin q, ∑ a2 : Fin q,
          g ⟨(a1 : ℤ), (a2 : ℤ)⟩ *
            ((∑' k : ℤ, F ((q : ℤ) * k + (a1 : ℤ))) *
             (∑' l : ℤ, H ((q : ℤ) * l + (a2 : ℤ)))) := by
  set psi : ((Fin q × Fin q) × (ℤ × ℤ)) → ℂ :=
    fun c => g ⟨(c.1.1 : ℤ), (c.1.2 : ℤ)⟩ *
      (F ((q : ℤ) * c.2.1 + (c.1.1 : ℤ)) * H ((q : ℤ) * c.2.2 + (c.1.2 : ℤ)))
    with hpsi
  have hψ : Summable psi := by
    rw [hpsi]; exact summable_class_summand q hq g F H hF hH
  have hg_eq : ∀ (a1 a2 : Fin q) (k l : ℤ),
      g ⟨(q : ℤ) * k + (a1 : ℤ), (q : ℤ) * l + (a2 : ℤ)⟩ = g ⟨(a1 : ℤ), (a2 : ℤ)⟩ := by
    intro a1 a2 k l
    refine hg _ _ ⟨⟨k, l⟩, ?_⟩
    ext <;> simp
  have hcongr : (∑' c : (Fin q × Fin q) × (ℤ × ℤ),
        (fun z : ℤ × ℤ => g ⟨z.1, z.2⟩ * (F z.1 * H z.2)) ((classEquiv q hq).symm c))
      = ∑' c, psi c := by
    apply tsum_congr
    rintro ⟨⟨a1, a2⟩, ⟨k, l⟩⟩
    simp only [hpsi, classEquiv_symm_apply q hq a1 a2 k l, hg_eq a1 a2 k l]
  rw [← Equiv.tsum_eq (classEquiv q hq).symm
    (fun z : ℤ × ℤ => g ⟨z.1, z.2⟩ * (F z.1 * H z.2)), hcongr]
  rw [Summable.tsum_prod hψ, tsum_fintype, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun a1 _ => ?_)
  refine Finset.sum_congr rfl (fun a2 _ => ?_)
  simp only [hpsi]
  rw [tsum_mul_left, tsum_prod_shift q hq F H hF hH (a1 : ℤ) (a2 : ℤ)]

/-- Reindexing a double `Fin q`-sum as a sum over the Finset `range q ×ˢ range q`. -/
lemma sum_fin_fin_eq_sum_product (q : ℕ) (f : ℕ → ℕ → ℂ) :
    (∑ a1 : Fin q, ∑ a2 : Fin q, f (a1 : ℕ) (a2 : ℕ))
      = ∑ α ∈ (Finset.range q).product (Finset.range q), f α.1 α.2 := by
  rw [Finset.product_eq_sprod, Finset.sum_product,
    Fin.sum_univ_eq_sum_range (fun i => ∑ a2 : Fin q, f i (a2 : ℕ)) q]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact Fin.sum_univ_eq_sum_range (fun j => f i j) q

theorem tsum_class_2d (q : ℕ) (hq : 0 < q) (g : GaussianInt → ℂ)
    (hg : ∀ z w : GaussianInt, (((q : ℤ) : GaussianInt) ∣ (z - w)) → g z = g w)
    (F H : ℤ → ℂ) (hF : Summable fun n : ℤ => F n) (hH : Summable fun n : ℤ => H n) :
    (∑' z : ℤ × ℤ, g ⟨z.1, z.2⟩ * (F z.1 * H z.2))
      = ∑ α ∈ (Finset.range q).product (Finset.range q),
          g ⟨α.1, α.2⟩ * ((∑' k : ℤ, F ((q : ℤ) * k + (α.1 : ℤ)))
                            * (∑' l : ℤ, H ((q : ℤ) * l + (α.2 : ℤ)))) := by
  rw [tsum_class_2d_fin q hq g hg F H hF hH]
  exact sum_fin_fin_eq_sum_product q (fun x y => g ⟨x, y⟩ *
    ((∑' k : ℤ, F ((q : ℤ) * k + (x : ℤ))) * (∑' l : ℤ, H ((q : ℤ) * l + (y : ℤ)))))

end Work.FIArea5.S16
