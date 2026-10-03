import Mathlib
import Submission.Work.Peluse.Basic

namespace Work.Peluse.Ulower

/-- **The residue-class sum is a decimated sum.**  For `c ≠ 0`, `r : ℕ` and `g : ℤ → ℂ` with
summable `ℓ¹`-norm, the sum over the residue class `x ≡ r (mod |c|)` equals the sum of the
decimated function `z ↦ g (c z + r)`:

`∑'_x (if |c| ∣ (x − r) then g x else 0) = ∑'_z g (c z + r)`.

This is the reindexing behind the "split `ℤ` into progressions modulo `|c|`" step of Peluse's
Lemma 3.9/8.1/9: `z ↦ c z + r` is a bijection from `ℤ` onto `{x : |c| ∣ x − r}` (with inverse
`x ↦ (x − r)/c`). -/
theorem ss_coset_sum {c : ℤ} (hc : c ≠ 0) (r : ℕ) {g : ℤ → ℂ}
    (hg : Summable fun x : ℤ => ‖g x‖) :
    (∑' x : ℤ, (if (c.natAbs : ℤ) ∣ (x - (r : ℤ)) then g x else 0))
      = ∑' z : ℤ, g (c * (z : ℤ) + (r : ℤ)) := by
  -- `(c.natAbs : ℤ) = |c|`, and `|c| ∣ m ↔ c ∣ m`, so the residue class is the image of
  -- `z ↦ c*z + r`, and `z ↦ c*z + r` is injective.
  have hdvd : ∀ x : ℤ, (c.natAbs : ℤ) ∣ (x - (r : ℤ)) ↔ c ∣ (x - (r : ℤ)) :=
    fun x => Int.natAbs_dvd
  let S : Set ℤ := {x | (c.natAbs : ℤ) ∣ (x - (r : ℤ))}
  have hmem : ∀ x : ℤ, x ∈ S ↔ (c.natAbs : ℤ) ∣ (x - (r : ℤ)) := fun x => Iff.rfl
  -- the two sides are the sums over `S`, resp. its pullback along the bijection
  have hL : (∑' x : ℤ, (if (c.natAbs : ℤ) ∣ (x - (r : ℤ)) then g x else 0))
      = ∑' x : S, g x := by
    rw [tsum_subtype S g]
    apply tsum_congr
    intro x
    rw [Set.indicator_apply]
    by_cases h : (c.natAbs : ℤ) ∣ (x - (r : ℤ))
    · rw [if_pos h, if_pos ((hmem x).mpr h)]
    · rw [if_neg h, if_neg (fun hx => h ((hmem x).mp hx))]
  -- the bijection `ℤ ≃ S`, `z ↦ c z + r`, with inverse `x ↦ (x - r)/c`
  let e : ℤ ≃ S :=
    { toFun := fun z => ⟨c * (z : ℤ) + (r : ℤ), by
        show (c.natAbs : ℤ) ∣ (c * (z : ℤ) + (r : ℤ)) - (r : ℤ)
        rw [add_sub_cancel_right]
        exact Int.natAbs_dvd.mpr (dvd_mul_right c z)⟩
      invFun := fun x => (x.1 - (r : ℤ)) / c
      left_inv := fun z => by
        show (c * (z : ℤ) + (r : ℤ) - (r : ℤ)) / c = z
        rw [add_sub_cancel_right, mul_comm]
        exact Int.mul_ediv_cancel z hc
      right_inv := fun x => by
        refine Subtype.ext ?_
        show c * ((x.1 - (r : ℤ)) / c) + (r : ℤ) = x.1
        rw [Int.mul_ediv_cancel' ((hdvd x.1).mp ((hmem x.1).mp x.2))]
        ring }
  calc (∑' x : ℤ, (if (c.natAbs : ℤ) ∣ (x - (r : ℤ)) then g x else 0))
      = ∑' x : S, g x := hL
    _ = ∑' z : ℤ, g (e z) := (Equiv.tsum_eq e (fun x : S => g x)).symm
    _ = ∑' z : ℤ, g (c * (z : ℤ) + (r : ℤ)) := tsum_congr (fun z => rfl)

end Work.Peluse.Ulower
