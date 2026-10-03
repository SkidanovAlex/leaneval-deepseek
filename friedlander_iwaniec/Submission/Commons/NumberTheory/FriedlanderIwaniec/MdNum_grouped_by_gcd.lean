import Mathlib
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_sum_sq_root_count_cubefree_eq
import Submission.Commons.NumberTheory.FriedlanderIwaniec.MdNum_reindex_squares

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.NumberTheory.FriedlanderIwaniec

open Finset

/-!
## Grouping a divisor sum of `MdNum` by the gcd of the summation index

`MdNum_reindex_squares` writes the left hand side of the identity as
`2 * ∑_{1 ≤ c ≤ √√x} N(c²) (2√(x - c⁴) + 1) + 2√x N(0)`, and
`sq_sum_sq_root_count_cubefree_eq` evaluates each `N(c²)` as
`gcd c d₂ · #{α : ZMod (d₁d₂/gcd c (d₁d₂)) | α² = -1}`.
The remaining step -- carried out here -- is a purely combinatorial regrouping of
`∑_c gcd c d₂ · M (gcd c (d₁d₂)) · w c` by the fibres of `c ↦ (gcd c d₁, gcd c d₂)`,
which for coprime `d₁, d₂` are exactly the fibres of `c ↦ gcd c (d₁d₂)`.
-/

/-- For coprime `d₁ d₂`, `gcd (ν₁ * ν₂) d₂ = ν₂` whenever `ν₁ ∣ d₁` and `ν₂ ∣ d₂`. -/
private lemma gcd_mul_right_eq_of_coprime {d₁ d₂ ν₁ ν₂ : ℕ} (hcop : Nat.Coprime d₁ d₂)
    (h₁ : ν₁ ∣ d₁) (h₂ : ν₂ ∣ d₂) : Nat.gcd (ν₁ * ν₂) d₂ = ν₂ := by
  refine Nat.dvd_antisymm ?_ (Nat.dvd_gcd (dvd_mul_left ν₂ ν₁) h₂)
  have hcg : Nat.Coprime (Nat.gcd (ν₁ * ν₂) d₂) ν₁ :=
    ((hcop.coprime_dvd_left h₁).coprime_dvd_right (Nat.gcd_dvd_right (ν₁ * ν₂) d₂)).symm
  have hdv : Nat.gcd (ν₁ * ν₂) d₂ ∣ ν₁ * ν₂ := Nat.gcd_dvd_left _ _
  exact hcg.dvd_of_dvd_mul_right (by simpa [Nat.mul_comm] using hdv)

/-- For coprime `d₁ d₂`, `gcd c (d₁ * d₂) = gcd c d₁ * gcd c d₂`. -/
private lemma gcd_eq_mul_gcd_of_coprime {d₁ d₂ c : ℕ} (hcop : Nat.Coprime d₁ d₂) :
    Nat.gcd c (d₁ * d₂) = Nat.gcd c d₁ * Nat.gcd c d₂ := by
  rw [Nat.gcd_comm c (d₁ * d₂), hcop.mul_gcd c, Nat.gcd_comm d₁ c, Nat.gcd_comm d₂ c]

/-- **Regrouping a divisor-weighted sum by gcd fibres.**  For coprime nonzero `d₁`, `d₂`,
any finite set `S` of natural numbers and any weights `M`, `w`,
`∑_{c ∈ S} gcd c d₂ · M (gcd c (d₁d₂)) · w c`
equals the double sum over `ν₁ ∣ d₁`, `ν₂ ∣ d₂` of `ν₂ · M (ν₁ν₂)` times the sum of
`w` over the `c ∈ S` with `gcd c (d₁d₂) = ν₁ν₂`. -/
private theorem sum_gcd_fiberwise_pair {d₁ d₂ : ℕ} (hs₁ : d₁ ≠ 0) (hs₂ : d₂ ≠ 0)
    (hcop : Nat.Coprime d₁ d₂) (S : Finset ℕ) (M w : ℕ → ℕ) :
    (∑ c ∈ S, Nat.gcd c d₂ * M (Nat.gcd c (d₁ * d₂)) * w c)
      = ∑ ν₁ ∈ Nat.divisors d₁, ∑ ν₂ ∈ Nat.divisors d₂,
          ν₂ * M (ν₁ * ν₂) *
            (∑ c ∈ S.filter (fun c => Nat.gcd c (d₁ * d₂) = ν₁ * ν₂), w c) := by
  classical
  have hmap : ∀ c ∈ S, (Nat.gcd c d₁, Nat.gcd c d₂) ∈ Nat.divisors d₁ ×ˢ Nat.divisors d₂ := by
    intro c _
    rw [Finset.mem_product]
    exact ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right c d₁, hs₁⟩,
           Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right c d₂, hs₂⟩⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmap
        (fun c => Nat.gcd c d₂ * M (Nat.gcd c (d₁ * d₂)) * w c)]
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun ν₁ hν₁ => Finset.sum_congr rfl fun ν₂ hν₂ => ?_
  have h₁ : ν₁ ∣ d₁ := (Nat.mem_divisors.mp hν₁).1
  have h₂ : ν₂ ∣ d₂ := (Nat.mem_divisors.mp hν₂).1
  have hiff : ∀ c : ℕ, ((Nat.gcd c d₁, Nat.gcd c d₂) = (ν₁, ν₂)) ↔
      (Nat.gcd c (d₁ * d₂) = ν₁ * ν₂) := by
    intro c
    constructor
    · intro h
      have h1 : Nat.gcd c d₁ = ν₁ := by simpa using congrArg Prod.fst h
      have h2 : Nat.gcd c d₂ = ν₂ := by simpa using congrArg Prod.snd h
      rw [gcd_eq_mul_gcd_of_coprime hcop, h1, h2]
    · intro h
      refine Prod.ext ?_ ?_
      · apply Nat.dvd_antisymm
        · have hcg : Nat.Coprime (Nat.gcd c d₁) ν₂ :=
            (hcop.coprime_dvd_right h₂).coprime_dvd_left (Nat.gcd_dvd_right c d₁)
          have hdv : Nat.gcd c d₁ ∣ ν₁ * ν₂ :=
            h ▸ Nat.dvd_gcd (Nat.gcd_dvd_left c d₁)
              ((Nat.gcd_dvd_right c d₁).trans (dvd_mul_right d₁ d₂))
          exact hcg.dvd_of_dvd_mul_right hdv
        · exact Nat.dvd_gcd
            (dvd_trans (dvd_mul_right ν₁ ν₂) (h ▸ Nat.gcd_dvd_left c (d₁ * d₂))) h₁
      · apply Nat.dvd_antisymm
        · have hcg : Nat.Coprime (Nat.gcd c d₂) ν₁ :=
            (hcop.symm.coprime_dvd_left (Nat.gcd_dvd_right c d₂)).coprime_dvd_right h₁
          have hdv : Nat.gcd c d₂ ∣ ν₁ * ν₂ :=
            h ▸ Nat.dvd_gcd (Nat.gcd_dvd_left c d₂)
              ((Nat.gcd_dvd_right c d₂).trans (dvd_mul_left d₂ d₁))
          exact hcg.dvd_of_dvd_mul_right (by simpa [Nat.mul_comm] using hdv)
        · exact Nat.dvd_gcd
            (dvd_trans (dvd_mul_left ν₂ ν₁) (h ▸ Nat.gcd_dvd_left c (d₁ * d₂))) h₂
  have hfil : S.filter (fun c => (Nat.gcd c d₁, Nat.gcd c d₂) = (ν₁, ν₂))
      = S.filter (fun c => Nat.gcd c (d₁ * d₂) = ν₁ * ν₂) :=
    Finset.filter_congr fun c _ => hiff c
  rw [hfil, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c hc => ?_
  have hcν : Nat.gcd c (d₁ * d₂) = ν₁ * ν₂ := (Finset.mem_filter.mp hc).2
  have hgc : Nat.gcd c d₂ = Nat.gcd (Nat.gcd c (d₁ * d₂)) d₂ := by
    rw [Nat.gcd_assoc, Nat.gcd_eq_right (dvd_mul_left d₂ d₁)]
  rw [hgc, hcν, gcd_mul_right_eq_of_coprime hcop h₁ h₂]

theorem MdNum_grouped_by_gcd {d₁ d₂ x : ℕ} (hs₁ : Squarefree d₁) (hs₂ : Squarefree d₂)
    (hcop : Nat.Coprime d₁ d₂) (h4 : ¬ 4 ∣ d₁ * d₂ ^ 2) :
    (∑ b ∈ Finset.range (Nat.sqrt x + 1),
        (if b = 0 then 1 else if Nat.sqrt b ^ 2 = b then 2 else 0) *
          ({α : ZMod (d₁ * d₂ ^ 2) | α ^ 2 + (b : ZMod (d₁ * d₂ ^ 2)) ^ 2 = 0}.ncard) *
          (2 * Nat.sqrt (x - b ^ 2) + 1))
      - ({α : ZMod (d₁ * d₂ ^ 2) | α ^ 2 = 0}.ncard)
    = 2 * (∑ ν₁ ∈ Nat.divisors d₁, ∑ ν₂ ∈ Nat.divisors d₂,
          ν₂ * ({α : ZMod ((d₁ * d₂) / (ν₁ * ν₂)) | α ^ 2 = -1}.ncard) *
            (∑ c ∈ (Finset.Icc 1 (Nat.sqrt (Nat.sqrt x))).filter
                (fun c => Nat.gcd c (d₁ * d₂) = ν₁ * ν₂),
              (2 * Nat.sqrt (x - c ^ 4) + 1)))
      + 2 * Nat.sqrt x * ({α : ZMod (d₁ * d₂ ^ 2) | α ^ 2 = 0}.ncard) := by
  classical
  have hd₁0 : d₁ ≠ 0 := hs₁.ne_zero
  have hd₂0 : d₂ ≠ 0 := hs₂.ne_zero
  have hD0 : 0 < d₁ * d₂ ^ 2 :=
    Nat.mul_pos (Nat.pos_of_ne_zero hd₁0) (Nat.pow_pos (Nat.pos_of_ne_zero hd₂0))
  -- Reindex the squares in the left hand side.
  rw [MdNum_reindex_squares (d₁ * d₂ ^ 2) x]
  -- Evaluate the root count at each square `c ^ 2` by the cubefree formula.
  have hterm : ∀ c : ℕ,
      ({α : ZMod (d₁ * d₂ ^ 2) | α ^ 2 + (((c ^ 2 : ℕ) : ZMod (d₁ * d₂ ^ 2))) ^ 2 = 0}.ncard)
        = Nat.gcd c d₂ *
            ((fun ν => ({α : ZMod ((d₁ * d₂) / ν) | α ^ 2 = -1}.ncard)) (Nat.gcd c (d₁ * d₂))) := by
    intro c
    have hset : {α : ZMod (d₁ * d₂ ^ 2) |
          α ^ 2 + (((c ^ 2 : ℕ) : ZMod (d₁ * d₂ ^ 2))) ^ 2 = 0}
        = {α : ZMod (d₁ * d₂ ^ 2) | α ^ 2 + ((c ^ 4 : ℕ) : ZMod (d₁ * d₂ ^ 2)) = 0} := by
      ext α
      simp only [Set.mem_ofPred_eq]
      rw [show (α : ZMod (d₁ * d₂ ^ 2)) ^ 2 + (((c ^ 2 : ℕ) : ZMod (d₁ * d₂ ^ 2))) ^ 2
            = (α : ZMod (d₁ * d₂ ^ 2)) ^ 2 + ((c ^ 4 : ℕ) : ZMod (d₁ * d₂ ^ 2)) from by
          push_cast; ring]
    rw [hset,
      sq_sum_sq_root_count_cubefree_eq (d := d₁ * d₂ ^ 2) (d₁ := d₁) (d₂ := d₂) (ℓ := c)
        hD0 rfl hs₁ hs₂ hcop h4]
  have hstep : (∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt x)),
        ({α : ZMod (d₁ * d₂ ^ 2) | α ^ 2 + (((c ^ 2 : ℕ) : ZMod (d₁ * d₂ ^ 2))) ^ 2 = 0}.ncard) *
          (2 * Nat.sqrt (x - c ^ 4) + 1))
      = ∑ c ∈ Finset.Icc 1 (Nat.sqrt (Nat.sqrt x)),
          Nat.gcd c d₂ *
            ((fun ν => ({α : ZMod ((d₁ * d₂) / ν) | α ^ 2 = -1}.ncard)) (Nat.gcd c (d₁ * d₂))) *
          (2 * Nat.sqrt (x - c ^ 4) + 1) := by
    apply Finset.sum_congr rfl
    intro c _
    rw [hterm c]
  rw [hstep]
  -- Regroup the remaining sum by the gcd fibres.
  rw [sum_gcd_fiberwise_pair (d₁ := d₁) (d₂ := d₂) hd₁0 hd₂0 hcop
        (Finset.Icc 1 (Nat.sqrt (Nat.sqrt x)))
        (fun ν => ({α : ZMod ((d₁ * d₂) / ν) | α ^ 2 = -1}.ncard))
        (fun c => 2 * Nat.sqrt (x - c ^ 4) + 1)]

end Commons.NumberTheory.FriedlanderIwaniec
