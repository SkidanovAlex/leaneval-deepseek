import Mathlib

namespace Work.LinnikAreas.BGTZ

open Finset

/-- The map sending a pair `(d, e)` to the triple `(gcd d e, d / gcd d e, e / gcd d e)`. -/
def gcdTriple (p : ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (Nat.gcd p.1 p.2, p.1 / Nat.gcd p.1 p.2, p.2 / Nat.gcd p.1 p.2)

/-- Flattening a sigma-type element `⟨g, (h, k)⟩` to the triple `(g, h, k)`. -/
def sigmaTriple (x : Σ _g : ℕ, ℕ × ℕ) : ℕ × ℕ × ℕ := (x.1, x.2.1, x.2.2)

/-- The sigma-indexed index set for the right hand side: `g` in `[1,R]`, and `(h,k)` in
`[1, R/g] × [1, R/g]`. -/
def bigSet (R : ℕ) : Finset (Σ _g : ℕ, ℕ × ℕ) :=
  (Finset.Icc 1 R).sigma fun g => (Finset.Icc 1 (R / g)) ×ˢ (Finset.Icc 1 (R / g))

/-- The set of triples `(g, h, k)` with `g ≤ R` and `h, k ≤ R / g`. -/
def tripleSet (R : ℕ) : Finset (ℕ × ℕ × ℕ) := (bigSet R).image sigmaTriple

lemma gcdTriple_injective : Function.Injective gcdTriple := by
  intro p q h
  have h1 : Nat.gcd p.1 p.2 = Nat.gcd q.1 q.2 := congrArg Prod.fst h
  have h2 : p.1 / Nat.gcd p.1 p.2 = q.1 / Nat.gcd q.1 q.2 := congrArg (fun t => t.2.1) h
  have h3 : p.2 / Nat.gcd p.1 p.2 = q.2 / Nat.gcd q.1 q.2 := congrArg (fun t => t.2.2) h
  have e1 : p.1 = q.1 := by
    calc p.1 = p.1 / Nat.gcd p.1 p.2 * Nat.gcd p.1 p.2 :=
          (Nat.div_mul_cancel (Nat.gcd_dvd_left p.1 p.2)).symm
      _ = q.1 / Nat.gcd q.1 q.2 * Nat.gcd p.1 p.2 := by rw [h2]
      _ = q.1 / Nat.gcd q.1 q.2 * Nat.gcd q.1 q.2 := by rw [h1]
      _ = q.1 := Nat.div_mul_cancel (Nat.gcd_dvd_left q.1 q.2)
  have e2 : p.2 = q.2 := by
    calc p.2 = p.2 / Nat.gcd p.1 p.2 * Nat.gcd p.1 p.2 :=
          (Nat.div_mul_cancel (Nat.gcd_dvd_right p.1 p.2)).symm
      _ = q.2 / Nat.gcd q.1 q.2 * Nat.gcd p.1 p.2 := by rw [h3]
      _ = q.2 / Nat.gcd q.1 q.2 * Nat.gcd q.1 q.2 := by rw [h1]
      _ = q.2 := Nat.div_mul_cancel (Nat.gcd_dvd_right q.1 q.2)
  exact Prod.ext e1 e2

lemma sigmaTriple_injective : Function.Injective sigmaTriple := by
  intro a b h
  obtain ⟨g, p⟩ := a
  obtain ⟨g', p'⟩ := b
  have hg : g = g' := congrArg Prod.fst h
  have hp1 : p.1 = p'.1 := congrArg (fun t => t.2.1) h
  have hp2 : p.2 = p'.2 := congrArg (fun t => t.2.2) h
  have hp : p = p' := Prod.ext hp1 hp2
  subst hp
  subst hg
  rfl

lemma gcdTriple_mem (R : ℕ) {p : ℕ × ℕ} (hp : p ∈ (Finset.Icc 1 R) ×ˢ (Finset.Icc 1 R)) :
    gcdTriple p ∈ tripleSet R := by
  rw [tripleSet, Finset.mem_image]
  refine ⟨⟨Nat.gcd p.1 p.2, (p.1 / Nat.gcd p.1 p.2, p.2 / Nat.gcd p.1 p.2)⟩, ?_, rfl⟩
  rw [bigSet, Finset.mem_sigma, Finset.mem_product]
  rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hp
  obtain ⟨⟨hp1a, hp1b⟩, hp2a, hp2b⟩ := hp
  have hgpos : 0 < Nat.gcd p.1 p.2 := Nat.gcd_pos_of_pos_left p.2 (by omega)
  have hgle1 : Nat.gcd p.1 p.2 ≤ p.1 := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left p.1 p.2)
  have hgle2 : Nat.gcd p.1 p.2 ≤ p.2 := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right p.1 p.2)
  rw [Finset.mem_Icc, Finset.mem_Icc, Finset.mem_Icc]
  refine ⟨⟨Nat.succ_le_of_lt hgpos, le_trans hgle1 hp1b⟩,
    ⟨⟨?_, Nat.div_le_div_right hp1b⟩, ⟨?_, Nat.div_le_div_right hp2b⟩⟩⟩
  · exact Nat.succ_le_of_lt (Nat.div_pos hgle1 hgpos)
  · exact Nat.succ_le_of_lt (Nat.div_pos hgle2 hgpos)

theorem gcdDivReindex (R : ℕ) (F : ℕ → ℕ → ℕ → ℝ) (hF : ∀ g h k, 0 ≤ F g h k) :
    (∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R,
        F (Nat.gcd d e) (d / Nat.gcd d e) (e / Nat.gcd d e))
      ≤ ∑ g ∈ Finset.Icc 1 R, ∑ h ∈ Finset.Icc 1 (R / g), ∑ k ∈ Finset.Icc 1 (R / g), F g h k := by
  calc (∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R,
          F (Nat.gcd d e) (d / Nat.gcd d e) (e / Nat.gcd d e))
      = ∑ p ∈ (Finset.Icc 1 R) ×ˢ (Finset.Icc 1 R),
          F (gcdTriple p).1 (gcdTriple p).2.1 (gcdTriple p).2.2 :=
          (Finset.sum_product (Finset.Icc 1 R) (Finset.Icc 1 R)
            (fun z => F (Nat.gcd z.1 z.2) (z.1 / Nat.gcd z.1 z.2)
              (z.2 / Nat.gcd z.1 z.2))).symm
    _ = ∑ q ∈ ((Finset.Icc 1 R) ×ˢ (Finset.Icc 1 R)).image gcdTriple,
          F q.1 q.2.1 q.2.2 :=
          (Finset.sum_image (s := (Finset.Icc 1 R) ×ˢ (Finset.Icc 1 R)) (g := gcdTriple)
            (f := fun q => F q.1 q.2.1 q.2.2)
            (fun a _ b _ hab => gcdTriple_injective hab)).symm
    _ ≤ ∑ q ∈ tripleSet R, F q.1 q.2.1 q.2.2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro q hq
            obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
            exact gcdTriple_mem R hp
          · intro q _ _
            exact hF q.1 q.2.1 q.2.2
    _ = ∑ g ∈ Finset.Icc 1 R, ∑ h ∈ Finset.Icc 1 (R / g),
          ∑ k ∈ Finset.Icc 1 (R / g), F g h k := by
          rw [tripleSet, Finset.sum_image
            (s := bigSet R) (g := sigmaTriple) (f := fun q => F q.1 q.2.1 q.2.2)
            (fun a _ b _ hab => sigmaTriple_injective hab)]
          rw [bigSet, Finset.sum_sigma]
          refine Finset.sum_congr rfl (fun g _ => ?_)
          rw [Finset.sum_product]
          rfl

end Work.LinnikAreas.BGTZ
