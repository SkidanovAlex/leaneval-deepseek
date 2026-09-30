import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

theorem prod_drop_bounds {n m d : ℕ} (hm : 1 ≤ m) (hd : 1 ≤ d)
    (h : Fin n → ℝ) (hh : ∀ i, 1 / (d : ℝ) ≤ h i)
    (e : Fin m → Fin n) (he : Function.Injective e) (j0 : Fin m)
    (hmax : ∀ j : Fin m, h (e j) ≤ h (e j0)) :
    (1 / (d : ℝ)) ^ m ≤ ∏ j : Fin m, h (e j) ∧
    (∏ j : Fin m, h (e j)) ≤ (h (e j0)) ^ m ∧
    1 / (d : ℝ) ≤ h (e j0) ∧
    (∏ j : Fin m, h (e j)) / h (e j0) / (d : ℝ) ^ (n - m) ≤
      ∏ i ∈ Finset.univ.erase (e j0), h i := by
  have _hm : 1 ≤ m := hm
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < (d : ℝ) := lt_of_lt_of_le zero_lt_one hd1
  have hcpos : 0 < 1 / (d : ℝ) := one_div_pos.mpr hdpos
  have hcnonneg : (0 : ℝ) ≤ 1 / (d : ℝ) := le_of_lt hcpos
  have hpos : ∀ i, 0 < h i := fun i => lt_of_lt_of_le hcpos (hh i)
  have hnonneg : ∀ i, 0 ≤ h i := fun i => le_of_lt (hpos i)
  -- (1) each factor is at least `1 / d`
  have h1 : (1 / (d : ℝ)) ^ m ≤ ∏ j : Fin m, h (e j) := by
    have := Finset.prod_le_prod₀ (s := Finset.univ)
      (f := fun _ : Fin m => 1 / (d : ℝ)) (g := fun j => h (e j))
      (fun _ _ => hcnonneg) (fun j _ => hh (e j))
    simpa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using this
  -- (2) each factor is at most the maximum
  have h2 : (∏ j : Fin m, h (e j)) ≤ (h (e j0)) ^ m := by
    have := Finset.prod_le_prod₀ (s := Finset.univ)
      (f := fun j : Fin m => h (e j)) (g := fun _ => h (e j0))
      (fun j _ => hnonneg (e j)) (fun j _ => hmax j)
    simpa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using this
  have h3 : 1 / (d : ℝ) ≤ h (e j0) := hh (e j0)
  -- The product over the index set of `e` is the product over `Fin m`.
  have hprod_image : (∏ i ∈ Finset.univ.image e, h i) = ∏ j : Fin m, h (e j) :=
    Finset.prod_image (s := Finset.univ) (g := e) (f := h) he.injOn
  -- The complement of the image of `e` inside `univ` has `n - m` elements.
  have hcard : (Finset.univ \ Finset.univ.image e).card = n - m := by
    have h1 : (Finset.univ \ Finset.univ.image e).card =
        (Finset.univ : Finset (Fin n)).card - (Finset.univ.image e).card := by
      rw [Finset.card_sdiff, Finset.inter_univ]
    rw [h1, Finset.card_image_of_injective (Finset.univ : Finset (Fin m)) he,
      Finset.card_univ, Finset.card_univ, Fintype.card_fin, Fintype.card_fin]
  -- Hence the product over the complement is at least `(1 / d) ^ (n - m)`.
  have hprod_ge : (1 / (d : ℝ)) ^ (n - m) ≤ ∏ i ∈ Finset.univ \ Finset.univ.image e, h i := by
    rw [← hcard]
    have := Finset.prod_le_prod₀ (s := Finset.univ \ Finset.univ.image e)
      (f := fun _ => 1 / (d : ℝ)) (g := h) (fun _ _ => hcnonneg) (fun i _ => hh i)
    simpa [Finset.prod_const] using this
  -- Splitting the total product off the image of `e`.
  have hmain : (∏ i ∈ Finset.univ.image e, h i) * (1 / (d : ℝ)) ^ (n - m) ≤
      ∏ i ∈ Finset.univ, h i := by
    have hsd := Finset.prod_sdiff (s₁ := Finset.univ.image e) (s₂ := Finset.univ) (f := h)
      (Finset.subset_univ _)
    rw [← hsd]
    have hnn : 0 ≤ ∏ i ∈ Finset.univ.image e, h i := Finset.prod_nonneg (fun i _ => hnonneg i)
    calc (∏ i ∈ Finset.univ.image e, h i) * (1 / (d : ℝ)) ^ (n - m)
        ≤ (∏ i ∈ Finset.univ.image e, h i) *
            (∏ i ∈ Finset.univ \ Finset.univ.image e, h i) :=
          mul_le_mul_of_nonneg_left hprod_ge hnn
      _ = (∏ i ∈ Finset.univ \ Finset.univ.image e, h i) *
            (∏ i ∈ Finset.univ.image e, h i) := by ring
  -- Erasing the maximising index divides by its value.
  have herase : ∏ i ∈ Finset.univ.erase (e j0), h i = (∏ i ∈ Finset.univ, h i) / h (e j0) := by
    rw [eq_div_iff (ne_of_gt (hpos (e j0)))]
    exact Finset.prod_erase_mul Finset.univ h (Finset.mem_univ (e j0))
  have key : (∏ i ∈ Finset.univ.image e, h i) * (1 / (d : ℝ)) ^ (n - m) / h (e j0) ≤
      (∏ i ∈ Finset.univ, h i) / h (e j0) :=
    div_le_div_of_nonneg_right hmain (le_of_lt (hpos (e j0)))
  -- (4) the drop bound
  have h4 : (∏ j : Fin m, h (e j)) / h (e j0) / (d : ℝ) ^ (n - m) ≤
      ∏ i ∈ Finset.univ.erase (e j0), h i := by
    rw [← hprod_image]
    have hLHS : (∏ i ∈ Finset.univ.image e, h i) / h (e j0) / (d : ℝ) ^ (n - m) =
        (∏ i ∈ Finset.univ.image e, h i) * (1 / (d : ℝ)) ^ (n - m) / h (e j0) := by
      rw [one_div_pow]
      ring
    rw [hLHS, herase]
    exact key
  exact ⟨h1, h2, h3, h4⟩

end Work.BW
