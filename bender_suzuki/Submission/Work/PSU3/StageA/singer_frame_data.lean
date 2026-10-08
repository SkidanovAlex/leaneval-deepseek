/-
# Singer frame data for `PSU3` Stage A

This module delivers `Work.PSU3.StageA.singer_frame_data`, the strengthened form of
`Work.PSU3.StageA.singer_data` in which the ring embedding `ι : F →+* E n` is required to be
*onto* the fixed field of the Frobenius `σE`.

The extra content over `singer_data` is one cardinality statement: the fixed field
`E^σ = {y : E n // σE y = y}` of the `2ⁿ`-power Frobenius on `E n = GF(2^(2n))` has exactly
`2 ^ n = |F|` elements (`Work.PSU3.GaloisField.fixedField_card`).  As `ι` is injective and lands
in `E^σ`, an injective map of finite sets of equal cardinality, it is onto `E^σ`.
-/
import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.GaloisField.fixedField_card
import Submission.Work.PSU3.StageA.singer_data

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

namespace Work.PSU3.StageA

/-- **The fixed field of `σE` in `E n` has `2 ^ n` elements.**  This is
`Work.PSU3.GaloisField.fixedField_card` with `Work.PSU3.σE` written in place of the explicit
`iterateFrobenius` (they are the same map for the instance `galoisFieldFrobInv`). -/
theorem ncard_fixedField (n : ℕ) (hn : 1 ≤ n) :
    Nat.card {y : Work.PSU3.E n // Work.PSU3.σE y = y} = 2 ^ n :=
  Work.PSU3.GaloisField.fixedField_card n hn

/-- An injective map from `F` (with `|F| = 2 ^ n`) into the fixed field of `σE` in `E n` is
surjective.  This is the cardinality step of `singer_frame_data`. -/
theorem surjective_of_injective_fixedField {n : ℕ} (hn : 1 ≤ n) {F : Type} [Field F] [Fintype F]
    (hcard : Nat.card F = 2 ^ n) (ι : F →+* Work.PSU3.E n)
    (hfix : ∀ c : F, Work.PSU3.σE (ι c) = ι c) (hinj : Function.Injective ι) :
    ∀ y : Work.PSU3.E n, Work.PSU3.σE y = y → ∃ c : F, ι c = y := by
  intro y hy
  let φ : F → {y : Work.PSU3.E n // Work.PSU3.σE y = y} := fun c => ⟨ι c, hfix c⟩
  have hφinj : Function.Injective φ := fun a b hab => hinj (Subtype.ext_iff.mp hab)
  have hcardS : Nat.card {y : Work.PSU3.E n // Work.PSU3.σE y = y} = Nat.card F := by
    rw [ncard_fixedField n hn, ← hcard]
  have hrange : Set.range φ = Set.univ := by
    refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_
    rw [Set.ncard_range_of_injective hφinj, Set.ncard_univ, hcardS]
  have hmem : (⟨y, hy⟩ : {y : Work.PSU3.E n // Work.PSU3.σE y = y}) ∈ Set.range φ := by
    rw [hrange]; exact Set.mem_univ _
  obtain ⟨c, hc⟩ := hmem
  exact ⟨c, Subtype.ext_iff.mp hc⟩

theorem singer_frame_data {n : ℕ} (hn : 1 ≤ n) (F : Type) [Field F] [Fintype F]
    (hcard : Nat.card F = 2 ^ n) (T : F × F →ₗ[F] F × F)
    (hfpf : ∀ v : F × F, T v = v → v = 0)
    (hdvd : orderOf T ∣ Nat.card F + 1) :
    ∃ (e : (Work.PSU3.E n)ˣ) (ι : F →+* Work.PSU3.E n) (β : F × F → Work.PSU3.E n),
      (e : Work.PSU3.E n) * Work.PSU3.σE (e : Work.PSU3.E n) = 1 ∧
      orderOf e = orderOf T ∧
      (∀ c : F, Work.PSU3.σE (ι c) = ι c) ∧ Function.Injective ι ∧
      (∀ y : Work.PSU3.E n, Work.PSU3.σE y = y → ∃ c : F, ι c = y) ∧
      (∀ a b : F × F, β (a + b) = β a + β b) ∧ Function.Bijective β ∧
      (∀ v : F × F, β (T v) = (e : Work.PSU3.E n) * β v) ∧
      (∀ (c : F) (v : F × F), β (c • v) = ι c * β v) := by
  obtain ⟨e, ι, β, hnorm, hord, hfix, hinj, hadd, hbij, heig, hsem⟩ :=
    singer_data hn F hcard T hfpf hdvd
  exact ⟨e, ι, β, hnorm, hord, hfix, hinj, surjective_of_injective_fixedField hn hcard ι hfix hinj,
    hadd, hbij, heig, hsem⟩

end Work.PSU3.StageA
