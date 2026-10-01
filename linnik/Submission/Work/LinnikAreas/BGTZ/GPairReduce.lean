import Mathlib
import Submission.Work.LinnikAreas.BGTZ.GEstimateDefs
import Submission.Work.LinnikAreas.BGTZ.gcdDivReindex

/-!
# The reduction `gpairsum ≤ Σ_g gw(g) (gsum(R/g))²` of BGTZ Lemma 4.3

Write `F n = gw χ₁ n`.  For the double sum of BGTZ Lemma 4.3 one has, for squarefree `d, e` with
`g = gcd d e`, the prime-wise identity

`F (lcm d e) · F (gcd d e) = F d · F e`,

i.e. `F (lcm d e) = F g · F (d/g) · F (e/g)`, because `d`, `e` and `lcm d e` are squarefree and
`lcm d e · gcd d e = d · e` (equivalently: both sides are the product of `gwt p` over
`p | lcm d e` counted with the multiplicity of the `gcd`).

The map `(d,e) ↦ (gcd d e, d / gcd d e, e / gcd d e)` is injective on the pairs `d, e ≤ R`; its
image consists of triples with `1 ≤ g ≤ R`, `1 ≤ h ≤ R/g`, `1 ≤ k ≤ R/g` (since `g·h = d ≤ R`).
Summing the pointwise bound over the image therefore gives

`gpairsum χ₁ R ≤ Σ_{g ≤ R} Σ_{h,k ≤ R/g} gw χ₁ g · gw χ₁ h · gw χ₁ k
              = Σ_{g ≤ R} gw χ₁ g · (gsum χ₁ (R/g))²`,

which is the statement.  The pure reindexing inequality is `gcdDivReindex`.
-/

open Finset

namespace Work.LinnikAreas.BGTZ

variable {q : ℕ} [NeZero q]

/-- `gw` is multiplicative over coprime arguments.  For coprime `a, b` either one of them is not
squarefree — and then so is `a * b` — or both are, in which case `a * b` is squarefree with
`primeFactors (a*b) = primeFactors a ∪ primeFactors b`, a disjoint union. -/
private lemma gw_mul_coprime (χ₁ : DirichletCharacter ℂ q) {a b : ℕ} (h : Nat.Coprime a b) :
    gw χ₁ (a * b) = gw χ₁ a * gw χ₁ b := by
  by_cases ha : Squarefree a
  · by_cases hb : Squarefree b
    · have hab : Squarefree (a * b) := (Nat.squarefree_mul h).mpr ⟨ha, hb⟩
      rw [gw_of_squarefree χ₁ hab, gw_of_squarefree χ₁ ha, gw_of_squarefree χ₁ hb,
        Nat.primeFactors_mul ha.ne_zero hb.ne_zero, Finset.prod_union h.disjoint_primeFactors]
    · have hab : ¬ Squarefree (a * b) := fun hab => hb ((Nat.squarefree_mul h).mp hab).2
      rw [gw_of_not_squarefree χ₁ hab, gw_of_not_squarefree χ₁ hb, mul_zero]
  · have hab : ¬ Squarefree (a * b) := fun hab => ha ((Nat.squarefree_mul h).mp hab).1
    rw [gw_of_not_squarefree χ₁ hab, gw_of_not_squarefree χ₁ ha, zero_mul]

/-- If `d` is squarefree and `g = gcd d e` then `g` and the cofactor `d / g` are coprime: a common
prime divisor would produce a square dividing `d = g · (d/g)`. -/
private lemma coprime_gcd_div_of_squarefree {d e : ℕ} (hd : Squarefree d) :
    Nat.Coprime (Nat.gcd d e) (d / Nat.gcd d e) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  set c := Nat.gcd (Nat.gcd d e) (d / Nat.gcd d e) with hc
  have h1 : c ∣ Nat.gcd d e := Nat.gcd_dvd_left _ _
  have h2 : c ∣ d / Nat.gcd d e := Nat.gcd_dvd_right _ _
  have hmul : c * c ∣ d := by
    rw [← Nat.mul_div_cancel' (Nat.gcd_dvd_left d e)]
    exact mul_dvd_mul h1 h2
  have hu : IsUnit c := hd c hmul
  rwa [Nat.isUnit_iff] at hu

/-- `lcm d e = gcd d e · (d / gcd d e) · (e / gcd d e)`; equivalently `d = g h`, `e = g k`,
`lcm d e = g h k` with `g = gcd d e`. -/
private lemma lcm_eq_gcd_mul_div_mul_div (d e : ℕ) :
    Nat.lcm d e = Nat.gcd d e * (d / Nat.gcd d e) * (e / Nat.gcd d e) := by
  rcases eq_or_ne (Nat.gcd d e) 0 with hg | hg
  · have hd0 : d = 0 := by
      have h := Nat.gcd_dvd_left d e
      rw [hg] at h; exact Nat.eq_zero_of_zero_dvd h
    have he0 : e = 0 := by
      have h := Nat.gcd_dvd_right d e
      rw [hg] at h; exact Nat.eq_zero_of_zero_dvd h
    subst hd0; subst he0; simp
  · have hgpos : 0 < Nat.gcd d e := Nat.pos_of_ne_zero hg
    have h1 : Nat.gcd d e * (d / Nat.gcd d e) = d := Nat.mul_div_cancel' (Nat.gcd_dvd_left d e)
    have h2 : Nat.gcd d e * (e / Nat.gcd d e) = e := Nat.mul_div_cancel' (Nat.gcd_dvd_right d e)
    have hgl : Nat.gcd d e * Nat.lcm d e = d * e := Nat.gcd_mul_lcm d e
    have hde : d * e = (Nat.gcd d e * (d / Nat.gcd d e)) * (Nat.gcd d e * (e / Nat.gcd d e)) := by
      rw [h1, h2]
    have key : Nat.gcd d e * Nat.lcm d e =
        Nat.gcd d e * (Nat.gcd d e * (d / Nat.gcd d e) * (e / Nat.gcd d e)) := by
      rw [hgl, hde]; ring
    exact Nat.eq_of_mul_eq_mul_left hgpos key

/-- **The per-pair identity of BGTZ Lemma 4.3.**  For arbitrary `d, e ≥ 1` (the cases handled by
`by_cases`; the pointwise statement itself makes sense for all `d, e`)
`gw χ₁ (lcm d e) ≤ gw χ₁ (gcd d e) · gw χ₁ (d / gcd d e) · gw χ₁ (e / gcd d e)`.

When `d` and `e` are squarefree all three factors `gcd d e`, `d / gcd d e`, `e / gcd d e` are
pairwise coprime and squarefree, and `lcm d e` is their product, so multiplicativity of `gw`
(`gw_mul_coprime`) turns the two sides into the same product of local weights.  Otherwise
`gw (lcm d e) = 0`, which is `≤` the (non-negative) right hand side. -/
private lemma gw_lcm_le (χ₁ : DirichletCharacter ℂ q) (d e : ℕ) :
    gw χ₁ (Nat.lcm d e)
      ≤ gw χ₁ (Nat.gcd d e) * gw χ₁ (d / Nat.gcd d e) * gw χ₁ (e / Nat.gcd d e) := by
  by_cases hd : Squarefree d
  · by_cases he : Squarefree e
    · have hgh : Nat.Coprime (Nat.gcd d e) (d / Nat.gcd d e) := coprime_gcd_div_of_squarefree hd
      have hgk : Nat.Coprime (Nat.gcd d e) (e / Nat.gcd d e) := by
        have h := coprime_gcd_div_of_squarefree (d := e) (e := d) he
        rwa [Nat.gcd_comm] at h
      have hhk : Nat.Coprime (d / Nat.gcd d e) (e / Nat.gcd d e) :=
        Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left e (Nat.pos_of_ne_zero hd.ne_zero))
      have hghk : Nat.Coprime (Nat.gcd d e * (d / Nat.gcd d e)) (e / Nat.gcd d e) :=
        hgk.mul_left hhk
      rw [lcm_eq_gcd_mul_div_mul_div d e, gw_mul_coprime χ₁ hghk, gw_mul_coprime χ₁ hgh]
    · have hns : ¬ Squarefree (Nat.lcm d e) :=
        fun h => he (Squarefree.squarefree_of_dvd (Nat.dvd_lcm_right d e) h)
      rw [gw_of_not_squarefree χ₁ hns]
      have a1 := gw_nonneg χ₁ (Nat.gcd d e)
      have a2 := gw_nonneg χ₁ (d / Nat.gcd d e)
      have a3 := gw_nonneg χ₁ (e / Nat.gcd d e)
      positivity
  · have hns : ¬ Squarefree (Nat.lcm d e) :=
      fun h => hd (Squarefree.squarefree_of_dvd (Nat.dvd_lcm_left d e) h)
    rw [gw_of_not_squarefree χ₁ hns]
    have a1 := gw_nonneg χ₁ (Nat.gcd d e)
    have a2 := gw_nonneg χ₁ (d / Nat.gcd d e)
    have a3 := gw_nonneg χ₁ (e / Nat.gcd d e)
    positivity

/-- `Σ_{h ≤ S} Σ_{k ≤ S} c · w h · w k = c · (Σ_{h ≤ S} w h)²`. -/
private lemma triple_sum_eq (c : ℝ) (S : Finset ℕ) (w : ℕ → ℝ) :
    (∑ h ∈ S, ∑ k ∈ S, c * w h * w k) = c * (∑ h ∈ S, w h) ^ 2 := by
  rw [pow_two, Finset.sum_mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro h _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro k _
  ring

theorem GPairReduce :
    ∀ (q : ℕ) [NeZero q] (χ₁ : DirichletCharacter ℂ q), χ₁ ^ 2 = 1 → ∀ R : ℕ,
      Work.LinnikAreas.BGTZ.gpairsum χ₁ R ≤ ∑ g ∈ Finset.Icc 1 R,
        Work.LinnikAreas.BGTZ.gw χ₁ g * (Work.LinnikAreas.BGTZ.gsum χ₁ (R / g)) ^ 2 := by
  intro q _ χ₁ _ R
  -- the double sum, dominated term by term by the triple `(gcd, cofactor, cofactor)`
  have h1 : gpairsum χ₁ R ≤ ∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R,
      gw χ₁ (Nat.gcd d e) * gw χ₁ (d / Nat.gcd d e) * gw χ₁ (e / Nat.gcd d e) := by
    unfold gpairsum
    exact Finset.sum_le_sum (fun d _ => Finset.sum_le_sum (fun e _ => gw_lcm_le χ₁ d e))
  -- reindex the injective map `(d,e) ↦ (gcd d e, d/gcd, e/gcd)` into the triple sum
  have h2 : (∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R,
      gw χ₁ (Nat.gcd d e) * gw χ₁ (d / Nat.gcd d e) * gw χ₁ (e / Nat.gcd d e))
      ≤ ∑ g ∈ Finset.Icc 1 R, ∑ h ∈ Finset.Icc 1 (R / g),
          ∑ k ∈ Finset.Icc 1 (R / g), gw χ₁ g * gw χ₁ h * gw χ₁ k :=
    gcdDivReindex R (fun g h k => gw χ₁ g * gw χ₁ h * gw χ₁ k) (fun g h k => by
      have a1 := gw_nonneg χ₁ g; have a2 := gw_nonneg χ₁ h; have a3 := gw_nonneg χ₁ k
      positivity)
  -- the triple sum factorises as `Σ_g gw g · (gsum χ₁ (R/g))²`
  have h3 : (∑ g ∈ Finset.Icc 1 R, ∑ h ∈ Finset.Icc 1 (R / g),
          ∑ k ∈ Finset.Icc 1 (R / g), gw χ₁ g * gw χ₁ h * gw χ₁ k)
      = ∑ g ∈ Finset.Icc 1 R, gw χ₁ g * (gsum χ₁ (R / g)) ^ 2 := by
    apply Finset.sum_congr rfl
    intro g _
    rw [gsum]
    exact triple_sum_eq (gw χ₁ g) (Finset.Icc 1 (R / g)) (gw χ₁)
  exact le_trans h1 (le_trans h2 (le_of_eq h3))

end Work.LinnikAreas.BGTZ
