import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.ArcFinsetDefs
import Submission.Work.BourgainPlan.IonescuWainger.ArcSep
import Submission.Work.BourgainPlan.IonescuWainger.ZModArcs

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

/-! ## Reducing the numerator of an arc point modulo the denominator

The `Finset` version `sigmaAFinset A` of Tao's arc `Σ_A` (see `ArcFinsetDefs.lean`) lists the points
of exact denominator `Q_A` by *natural* numerators `a ∈ [0, Q_A)` coprime to `Q_A`, whereas the `Set`
version `sigmaA A` (`ArcDefs.lean`) uses *integer* numerators `a ∈ ℤ` with `gcd (a.natAbs, Q_A) = 1`.
The bridge is the reduction `a ↦ (a % Q_A).toNat`, which lands in `[0, Q_A)` and keeps both the arc
point (`Int.emod`: the numerators differ by a multiple of `Q_A`) and coprimality. -/

/-- **Coprimality is preserved by reducing the numerator modulo the denominator.**  If `a ∈ ℤ` is
coprime to `Q ≠ 0` then so is `a % Q` (taken as a natural number). -/
lemma coprime_emod_toNat {Q : ℕ} (hQ : Q ≠ 0) {a : ℤ} (h : Nat.Coprime a.natAbs Q) :
    Nat.Coprime (a % (Q : ℤ)).toNat Q := by
  have hQne : (Q : ℤ) ≠ 0 := by exact_mod_cast hQ
  have hnonneg : 0 ≤ a % (Q : ℤ) := Int.emod_nonneg a hQne
  have hcast : (((a % (Q : ℤ)).toNat : ℕ) : ℤ) = a % (Q : ℤ) := Int.toNat_of_nonneg hnonneg
  -- write `d` for the gcd we must show is `1`; keeping it opaque avoids rewriting inside it
  set d : ℕ := Nat.gcd (a % (Q : ℤ)).toNat Q with hd
  have h1 : d ∣ (a % (Q : ℤ)).toNat := by rw [hd]; exact Nat.gcd_dvd_left _ _
  have h2 : d ∣ Q := by rw [hd]; exact Nat.gcd_dvd_right _ _
  have h1' : (d : ℤ) ∣ ((a % (Q : ℤ)).toNat : ℤ) := by exact_mod_cast h1
  have h2' : (d : ℤ) ∣ (Q : ℤ) := by exact_mod_cast h2
  -- `d` divides `a % Q` and `Q`, and `a = a % Q + (a / Q) * Q`, so it divides `a` and hence `a.natAbs`
  have h3 : (d : ℤ) ∣ a := by
    have ha : a = ((a % (Q : ℤ)).toNat : ℤ) + (a / (Q : ℤ)) * (Q : ℤ) := by
      rw [hcast]
      have := Int.mul_ediv_add_emod a (Q : ℤ)
      linarith
    rw [ha]
    exact dvd_add h1' (dvd_mul_of_dvd_right h2' (a / (Q : ℤ)))
  have h4 : d ∣ a.natAbs := by
    have := (Int.natAbs_dvd_natAbs (a := (d : ℤ)) (b := a)).mpr h3
    simpa using this
  have h5 : d ∣ Nat.gcd a.natAbs Q := Nat.dvd_gcd h4 h2
  rw [Nat.coprime_iff_gcd_eq_one.mp h] at h5
  rw [Nat.coprime_iff_gcd_eq_one, ← hd]
  exact Nat.dvd_one.mp h5

/-- **The arc point depends only on the numerator modulo the denominator.**  For `Q ≠ 0` the point
`(a % Q)/Q` of the circle is the point `a/Q` (the numerators differ by a multiple of `Q`). -/
lemma arcPt_emod_toNat {Q : ℕ} (hQ : Q ≠ 0) (a : ℤ) :
    arcPt Q ((a % (Q : ℤ)).toNat : ℤ) = arcPt Q a := by
  have hQne : (Q : ℤ) ≠ 0 := by exact_mod_cast hQ
  have hnonneg : 0 ≤ a % (Q : ℤ) := Int.emod_nonneg a hQne
  rw [Int.toNat_of_nonneg hnonneg]
  refine (arcPt_eq_arcPt_iff_dvd hQ _ _).mpr ?_
  have hmod : (Q : ℤ) ∣ a - a % (Q : ℤ) := by
    have h := Int.mul_ediv_add_emod a (Q : ℤ)
    exact ⟨a / (Q : ℤ), by linarith⟩
  have hneg : (a % (Q : ℤ)) - a = -(a - a % (Q : ℤ)) := by ring
  rw [hneg]
  exact dvd_neg.mpr hmod

/-- The `Finset` of points of *exact* denominator `Q_A` (`sigmaAFinset`) is exactly Tao's arc
`Σ_A` (`sigmaA`, a `Set` of the circle): `↑(sigmaAFinset A) = sigmaA A` for `0 ∉ A` (equivalently
`Q_A ≠ 0`; this holds in every application, where `A ⊆ S` with the elements of `S` pairwise coprime
and `≥ 2`).  Together with the similar identities for `Σ_{⊆A}` this lets a support condition stated
for the `Set` version (`HasFreqSupport h hh (arcSet α ε)`, `BandLimitedL2Ortho.lean`) be used
together with sums over the `Finset` version (`Σ_{α ∈ sigmaAFinset A} f α`, the major arc system
`f_{Σ_A}` of Tao's `ortho-apply`).

Proof route: `⊆` is immediate from the definitions (the witnesses are `a < Q_A`); for `⊇`, an integer
witness `a` with `gcd (a, Q_A) = 1` reduces modulo `Q_A` to an `a₀ ∈ [0, Q_A)` with the same arc
point (`arcPt_commonDenom` / `arcPt_eq_arcPt_iff_dvd`) and `gcd (a₀, Q_A) = 1`. -/
theorem coe_sigmaAFinset {A : Finset ℕ} (hA0 : 0 ∉ A) :
    ((sigmaAFinset A : Finset Circle) : Set Circle) = sigmaA A := by
  have hQne : QA A ≠ 0 := QA_ne_zero fun q hq h => hA0 (h ▸ hq)
  have hQpos : (0 : ℤ) < (QA A : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hQne
  have hQne' : (QA A : ℤ) ≠ 0 := by exact_mod_cast hQne
  ext x
  constructor
  · -- every listed numerator `a < Q_A` is coprime to `Q_A`, hence exhibits `x` as a point of `Σ_A`
    intro hx
    rw [Finset.mem_coe, sigmaAFinset, Finset.mem_image] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨_, hcop⟩ := Finset.mem_filter.mp ha
    exact ⟨(a : ℤ), by simpa using hcop, rfl⟩
  · -- conversely an integer numerator coprime to `Q_A` is represented by its residue in `[0, Q_A)`
    intro hx
    rw [sigmaA] at hx
    obtain ⟨a, hcop, rfl⟩ := hx
    rw [Finset.mem_coe, sigmaAFinset, Finset.mem_image]
    have hnonneg : 0 ≤ a % (QA A : ℤ) := Int.emod_nonneg a hQne'
    have hlt : a % (QA A : ℤ) < (QA A : ℤ) := Int.emod_lt_of_pos a hQpos
    exact ⟨(a % (QA A : ℤ)).toNat,
      Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by rw [Int.toNat_lt hnonneg]; exact hlt),
          coprime_emod_toNat hQne hcop⟩,
      arcPt_emod_toNat hQne a⟩

end Work.BourgainPlan.IonescuWainger
