/-
# Work.Deep.Conc.prob_inter_eq_mul_of_determined

**Independence of two events determined by disjoint sets of coordinates** in the uniform
measure on a finite product space `Ω = ∀ i, π i` (`Work.Deep.Conc.prob`, the uniform
probability of `Work.Deep.Conc.Basic`).

If `X ⊆ Ω` depends only on the coordinates in a finite set `S` and `Y ⊆ Ω` depends only on
the coordinates in a finite set `T`, and `S` and `T` are disjoint, then

  `prob (X ∩ Y) = prob X * prob Y`.

## Proof

Everything is a finite sum, so no measure theory is needed.  Write `N = #Ω` and let
`1_E` be the indicator of `E`.  The proof is the standard "gluing" computation, done at
the level of the unnormalised sums `∑_ξ 1_E ξ`:

* `(∑ 1_X)(∑ 1_Y) = ∑_{p : Ω × Ω} 1_X p.1 * 1_Y p.2` (product of sums);
* pointwise, `1_X p.1 * 1_Y p.2 = 1_{X ∩ Y} (glue S p.1 p.2)`, where
  `glue S a b i = if i ∈ S then a i else b i`:
  the glued point agrees with `p.1` on `S` (so it lies in `X` iff `p.1` does) and with
  `p.2` on `T ⊆ Sᶜ` (so it lies in `Y` iff `p.2` does);
* the map `Φ : Ω × Ω → Ω × Ω`, `Φ (a, b) = (glue S a b, glue S b a)` is an involution
  (`swapGlue`), hence a bijection, and `(swapGlue S p).1 = glue S p.1 p.2`, so
  `∑_p 1_{X ∩ Y} (glue S p.1 p.2) = ∑_q 1_{X ∩ Y} q.1 = N * ∑_ξ 1_{X ∩ Y} ξ`
  (the last sum being over a product, the inner sum is constant).

Dividing the identity `(∑ 1_X)(∑ 1_Y) = N * ∑ 1_{X∩Y}` by `N ^ 2` (with `N ≠ 0`, which is
where `hne : ∀ i, Nonempty (π i)` is used) gives the claim.
-/
import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Conc.Pi

open scoped BigOperators

namespace Work.Deep.Conc

/-- Glue two points of the product space `∀ i, π i` along the coordinate set `S`:
the coordinates in `S` are taken from `a`, the others from `b`. -/
private def glue {ι : Type*} [DecidableEq ι] {π : ι → Type*} (S : Finset ι)
    (a b : ∀ i, π i) : ∀ i, π i :=
  fun i => if i ∈ S then a i else b i

/-- The involution of `Ω × Ω` obtained by swapping the two halves of the coordinates along
`S`: it sends `(a, b)` to `(glue S a b, glue S b a)`. -/
private def swapGlue {ι : Type*} [DecidableEq ι] {π : ι → Type*} (S : Finset ι) :
    (∀ i, π i) × (∀ i, π i) ≃ (∀ i, π i) × (∀ i, π i) where
  toFun p := (glue S p.1 p.2, glue S p.2 p.1)
  invFun p := (glue S p.1 p.2, glue S p.2 p.1)
  left_inv p := by
    show (glue S (glue S p.1 p.2) (glue S p.2 p.1),
        glue S (glue S p.2 p.1) (glue S p.1 p.2)) = p
    have h1 : glue S (glue S p.1 p.2) (glue S p.2 p.1) = p.1 := by
      funext i
      by_cases hi : i ∈ S <;> simp [glue, hi]
    have h2 : glue S (glue S p.2 p.1) (glue S p.1 p.2) = p.2 := by
      funext i
      by_cases hi : i ∈ S <;> simp [glue, hi]
    rw [h1, h2]
  right_inv p := by
    show (glue S (glue S p.1 p.2) (glue S p.2 p.1),
        glue S (glue S p.2 p.1) (glue S p.1 p.2)) = p
    have h1 : glue S (glue S p.1 p.2) (glue S p.2 p.1) = p.1 := by
      funext i
      by_cases hi : i ∈ S <;> simp [glue, hi]
    have h2 : glue S (glue S p.2 p.1) (glue S p.1 p.2) = p.2 := by
      funext i
      by_cases hi : i ∈ S <;> simp [glue, hi]
    rw [h1, h2]

theorem prob_inter_eq_mul_of_determined {ι : Type*} [Fintype ι] [DecidableEq ι]
    {π : ι → Type*} [∀ i, Fintype (π i)] (hne : ∀ i, Nonempty (π i)) {S T : Finset ι}
    (hST : Disjoint S T) {X Y : Set (∀ i, π i)}
    (hX : ∀ ξ ξ' : ∀ i, π i, (∀ i ∈ S, ξ i = ξ' i) → (ξ ∈ X ↔ ξ' ∈ X))
    (hY : ∀ ξ ξ' : ∀ i, π i, (∀ i ∈ T, ξ i = ξ' i) → (ξ ∈ Y ↔ ξ' ∈ Y)) :
    Work.Deep.Conc.prob (X ∩ Y) = Work.Deep.Conc.prob X * Work.Deep.Conc.prob Y := by
  classical
  -- `S` and `T` are disjoint, so a coordinate of `T` is never a coordinate of `S`.
  have hd : ∀ i, i ∈ T → i ∉ S := by
    intro i hiT hiS
    exact absurd (Finset.mem_inter.mpr ⟨hiS, hiT⟩)
      (by simp [Finset.disjoint_iff_inter_eq_empty.mp hST])
  -- Pointwise: the glue of the two halves of a point of `Ω × Ω` lies in `X ∩ Y` exactly when
  -- the first half lies in `X` and the second half lies in `Y`.
  have hpt : ∀ p : (∀ i, π i) × (∀ i, π i),
      X.indicator (fun _ => (1 : ℝ)) p.1 * Y.indicator (fun _ => (1 : ℝ)) p.2
        = (X ∩ Y).indicator (fun _ => (1 : ℝ)) (glue S p.1 p.2) := by
    intro p
    -- the glue agrees with the first component on `S` and with the second component on `T`
    have keyX : (glue S p.1 p.2 ∈ X ↔ p.1 ∈ X) :=
      hX (glue S p.1 p.2) p.1 (fun i hi => if_pos hi)
    have keyY : (glue S p.1 p.2 ∈ Y ↔ p.2 ∈ Y) :=
      hY (glue S p.1 p.2) p.2 (fun i hi => if_neg (hd i hi))
    by_cases ha : p.1 ∈ X
    · by_cases hb : p.2 ∈ Y
      · have hg : glue S p.1 p.2 ∈ X ∩ Y := Set.mem_inter (keyX.mpr ha) (keyY.mpr hb)
        rw [Set.indicator_of_mem ha (fun _ => (1 : ℝ)),
          Set.indicator_of_mem hb (fun _ => (1 : ℝ)),
          Set.indicator_of_mem hg (fun _ => (1 : ℝ))]
        norm_num
      · have hg : glue S p.1 p.2 ∉ X ∩ Y := fun h => hb (keyY.mp h.2)
        rw [Set.indicator_of_mem ha (fun _ => (1 : ℝ)),
          Set.indicator_of_notMem hb (fun _ => (1 : ℝ)),
          Set.indicator_of_notMem hg (fun _ => (1 : ℝ))]
        norm_num
    · have hg : glue S p.1 p.2 ∉ X ∩ Y := fun h => ha (keyX.mp h.1)
      rw [Set.indicator_of_notMem ha (fun _ => (1 : ℝ)),
        Set.indicator_of_notMem hg (fun _ => (1 : ℝ))]
      norm_num
  -- Sums are transferred by the involution `swapGlue`.
  have hsum : ∑ p : (∀ i, π i) × (∀ i, π i),
        (X ∩ Y).indicator (fun _ => (1 : ℝ)) (glue S p.1 p.2)
      = ∑ q : (∀ i, π i) × (∀ i, π i), (X ∩ Y).indicator (fun _ => (1 : ℝ)) q.1 :=
    Fintype.sum_equiv (swapGlue S) _ _ (fun p => rfl)
  -- Fubini: the expectation of a function of the first coordinate is the expectation itself.
  have hfco : ∀ f : (∀ i, π i) → ℝ,
      Work.Deep.Conc.expect (fun q : (∀ i, π i) × (∀ i, π i) => f q.1)
        = Work.Deep.Conc.expect f := by
    intro f
    have h1 : Work.Deep.Conc.expect (fun q : (∀ i, π i) × (∀ i, π i) => f q.1)
        = (∑ q : (∀ i, π i) × (∀ i, π i), f q.1)
          / (Fintype.card ((∀ i, π i) × (∀ i, π i)) : ℝ) := rfl
    have h2 : Work.Deep.Conc.expect f
        = (∑ u : (∀ i, π i), f u) / (Fintype.card (∀ i, π i) : ℝ) := rfl
    have hN : (Fintype.card (∀ i, π i) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp
        (Fintype.card_pos_iff.mpr ⟨fun i => Classical.choice (hne i)⟩))
    rw [h1, h2, Fintype.card_prod, Nat.cast_mul, Fintype.sum_prod_type]
    have hinner : ∀ u : ∀ i, π i,
        (∑ v : ∀ i, π i, f (u, v).1) = (Fintype.card (∀ i, π i) : ℝ) * f u := by
      intro u
      have hs : (∑ v : ∀ i, π i, f (u, v).1) = ∑ _v : ∀ i, π i, f u :=
        Finset.sum_congr rfl (fun v _ => rfl)
      rw [hs, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have houter : (∑ u : ∀ i, π i, ∑ v : ∀ i, π i, f (u, v).1)
        = ∑ u : ∀ i, π i, (Fintype.card (∀ i, π i) : ℝ) * f u :=
      Finset.sum_congr rfl (fun u _ => hinner u)
    rw [houter, ← Finset.mul_sum]
    exact mul_div_mul_left _ _ hN
  calc Work.Deep.Conc.prob (X ∩ Y)
      = Work.Deep.Conc.expect
          (fun q : (∀ i, π i) × (∀ i, π i) =>
            (X ∩ Y).indicator (fun _ => (1 : ℝ)) q.1) :=
        (hfco _).symm
    _ = Work.Deep.Conc.expect
          (fun p : (∀ i, π i) × (∀ i, π i) =>
            (X ∩ Y).indicator (fun _ => (1 : ℝ)) (glue S p.1 p.2)) := by
        rw [show Work.Deep.Conc.expect
              (fun q : (∀ i, π i) × (∀ i, π i) =>
                (X ∩ Y).indicator (fun _ => (1 : ℝ)) q.1)
              = (∑ q : (∀ i, π i) × (∀ i, π i),
                    (X ∩ Y).indicator (fun _ => (1 : ℝ)) q.1)
                / (Fintype.card ((∀ i, π i) × (∀ i, π i)) : ℝ) from rfl,
            show Work.Deep.Conc.expect
              (fun p : (∀ i, π i) × (∀ i, π i) =>
                (X ∩ Y).indicator (fun _ => (1 : ℝ)) (glue S p.1 p.2))
              = (∑ p : (∀ i, π i) × (∀ i, π i),
                    (X ∩ Y).indicator (fun _ => (1 : ℝ)) (glue S p.1 p.2))
                / (Fintype.card ((∀ i, π i) × (∀ i, π i)) : ℝ) from rfl]
        rw [hsum]
    _ = Work.Deep.Conc.expect
          (fun p : (∀ i, π i) × (∀ i, π i) =>
            X.indicator (fun _ => (1 : ℝ)) p.1 * Y.indicator (fun _ => (1 : ℝ)) p.2) :=
        Work.Deep.Conc.expect_congr (fun p => (hpt p).symm)
    _ = Work.Deep.Conc.expect (X.indicator (fun _ => (1 : ℝ)))
          * Work.Deep.Conc.expect (Y.indicator (fun _ => (1 : ℝ))) :=
        Work.Deep.Conc.expect_prod_tensor _ _
    _ = Work.Deep.Conc.prob X * Work.Deep.Conc.prob Y := rfl

end Work.Deep.Conc
